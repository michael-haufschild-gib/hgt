import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Formation Stokes, Følner properness, and rank-width selection

Local formation current on a finite directed packet obeys an exact cut Stokes law. Absolute cut
traffic bounds the bulk character, and a uniform edge-current capacity turns this into a formation
isoperimetric inequality. Følner packet families select neutral current; nonneutrality forces
inverse-isoperimetric boundary-current growth. Box packets additionally expose the precise
channel-rank/width density required to sustain nonzero current.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section FiniteFormationStokes

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Signed incidence of an oriented edge at a vertex. -/
def formationIncidence (t h : E → V) (e : E) (v : V) : ℝ :=
  (if h e = v then 1 else 0) - (if t e = v then 1 else 0)

/-- Net formation current entering a vertex. -/
def formationDivergence (t h : E → V) (J : E → ℝ) (v : V) : ℝ :=
  ∑ e : E, formationIncidence t h e v * J e

/-- Total incidence of one edge against an observed finite interior. -/
def formationCutCoefficient (t h : E → V) (S : Finset V) (e : E) : ℝ :=
  ∑ v ∈ S, formationIncidence t h e v

/-- Oriented current crossing an observed cut. -/
def formationCutFlux (t h : E → V) (S : Finset V) (J : E → ℝ) : ℝ :=
  ∑ e : E, formationCutCoefficient t h S e * J e

/-- Positive total variation of current crossing an observed cut. -/
def formationCutTraffic (t h : E → V) (S : Finset V) (J : E → ℝ) : ℝ :=
  ∑ e : E, |formationCutCoefficient t h S e * J e|

/-- Edges with exactly one endpoint in the observed interior. -/
def formationEdgeBoundary (t h : E → V) (S : Finset V) : Finset E :=
  Finset.univ.filter fun e => (h e ∈ S) ≠ (t e ∈ S)

omit [Fintype V] [DecidableEq E] in
/-- **Finite formation Stokes law.** Summed local divergence is exactly oriented cut flux. -/
theorem sum_formationDivergence_eq_formationCutFlux
    (t h : E → V) (S : Finset V) (J : E → ℝ) :
    ∑ v ∈ S, formationDivergence t h J v = formationCutFlux t h S J := by
  simp only [formationDivergence, formationCutFlux, formationCutCoefficient]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_mul]

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Cut incidence is the difference of endpoint-membership indicators. -/
theorem formationCutCoefficient_eq
    (t h : E → V) (S : Finset V) (e : E) :
    formationCutCoefficient t h S e =
      (if h e ∈ S then 1 else 0) - (if t e ∈ S then 1 else 0) := by
  simp [formationCutCoefficient, formationIncidence, Finset.sum_sub_distrib]

omit [Fintype V] in
/-- Absolute cut incidence is exactly the boundary-edge indicator. -/
theorem abs_formationCutCoefficient_eq_indicator_boundary
    (t h : E → V) (S : Finset V) (e : E) :
    |formationCutCoefficient t h S e| =
      if e ∈ formationEdgeBoundary t h S then 1 else 0 := by
  rw [formationCutCoefficient_eq]
  by_cases hh : h e ∈ S <;> by_cases ht : t e ∈ S <;>
    simp [formationEdgeBoundary, hh, ht]

omit [Fintype V] [DecidableEq E] in
/-- Positive cut traffic dominates oriented flux. -/
theorem abs_formationCutFlux_le_formationCutTraffic
    (t h : E → V) (S : Finset V) (J : E → ℝ) :
    |formationCutFlux t h S J| ≤ formationCutTraffic t h S J := by
  exact Finset.abs_sum_le_sum_abs _ _

omit [Fintype V] in
/-- Cut traffic is exactly the sum of absolute currents on boundary edges. -/
theorem formationCutTraffic_eq_sum_boundary_abs
    (t h : E → V) (S : Finset V) (J : E → ℝ) :
    formationCutTraffic t h S J = ∑ e ∈ formationEdgeBoundary t h S, |J e| := by
  rw [formationCutTraffic]
  calc
    ∑ e : E, |formationCutCoefficient t h S e * J e| =
        ∑ e : E, if e ∈ formationEdgeBoundary t h S then |J e| else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [abs_mul, abs_formationCutCoefficient_eq_indicator_boundary]
      by_cases he : e ∈ formationEdgeBoundary t h S <;> simp [he]
    _ = ∑ e ∈ formationEdgeBoundary t h S, |J e| := by
      rw [formationEdgeBoundary, Finset.sum_filter]
      simp

omit [Fintype V] in
/-- A uniform local edge-current bound controls total cut traffic by boundary cardinality. -/
theorem formationCutTraffic_le_card_mul_of_edgeBound
    (t h : E → V) (S : Finset V) (J : E → ℝ) (M : ℝ)
    (hJ : ∀ e : E, |J e| ≤ M) :
    formationCutTraffic t h S J ≤ (formationEdgeBoundary t h S).card * M := by
  rw [formationCutTraffic_eq_sum_boundary_abs]
  calc
    ∑ e ∈ formationEdgeBoundary t h S, |J e|
        ≤ ∑ _e ∈ formationEdgeBoundary t h S, M :=
      Finset.sum_le_sum fun e _ => hJ e
    _ = (formationEdgeBoundary t h S).card * M := by simp

omit [Fintype V] [DecidableEq E] in
/-- Constant bulk divergence times packet volume is bounded by positive cut traffic. -/
theorem card_mul_abs_bulkCurrent_le_cutTraffic
    (t h : E → V) (S : Finset V) (J : E → ℝ) (chi : ℝ)
    (hbulk : ∀ v ∈ S, formationDivergence t h J v = chi) :
    (S.card : ℝ) * |chi| ≤ formationCutTraffic t h S J := by
  have hsum : (∑ v ∈ S, formationDivergence t h J v) = (S.card : ℝ) * chi := by
    calc
      ∑ v ∈ S, formationDivergence t h J v = ∑ _v ∈ S, chi :=
        Finset.sum_congr rfl hbulk
      _ = (S.card : ℝ) * chi := by simp
  have habscard : |(S.card : ℝ)| = (S.card : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg S.card)
  calc
    (S.card : ℝ) * |chi| = |(S.card : ℝ) * chi| := by
      rw [abs_mul, habscard]
    _ = |formationCutFlux t h S J| := by
      rw [← sum_formationDivergence_eq_formationCutFlux, hsum]
    _ ≤ formationCutTraffic t h S J :=
      abs_formationCutFlux_le_formationCutTraffic t h S J

omit [Fintype V] in
/-- **Formation Cheeger bound.** Bulk current is bounded by boundary size times local capacity. -/
theorem card_mul_abs_bulkCurrent_le_boundaryCapacity
    (t h : E → V) (S : Finset V) (J : E → ℝ) (chi M : ℝ)
    (hbulk : ∀ v ∈ S, formationDivergence t h J v = chi)
    (hJ : ∀ e : E, |J e| ≤ M) :
    (S.card : ℝ) * |chi| ≤ (formationEdgeBoundary t h S).card * M :=
  (card_mul_abs_bulkCurrent_le_cutTraffic t h S J chi hbulk).trans
    (formationCutTraffic_le_card_mul_of_edgeBound t h S J M hJ)

end FiniteFormationStokes

universe u

/-- A finite local formation packet with constant bulk divergence and uniform edge-current
capacity. Vertex and edge types may vary across packet families. -/
structure FiniteLocalFormationPacket (chi M : ℝ) where
  V : Type u
  [fintypeV : Fintype V]
  [decidableEqV : DecidableEq V]
  E : Type u
  [fintypeE : Fintype E]
  [decidableEqE : DecidableEq E]
  tail : E → V
  head : E → V
  interior : Finset V
  current : E → ℝ
  bulk : ∀ x ∈ interior, formationDivergence tail head current x = chi
  edgeBound : ∀ e : E, |current e| ≤ M

namespace FiniteLocalFormationPacket

/-- Bulk volume of a finite formation packet. -/
def volume {chi M : ℝ} (P : FiniteLocalFormationPacket chi M) : ℕ :=
  P.interior.card

/-- Cut boundary of a finite formation packet. -/
def boundary {chi M : ℝ} (P : FiniteLocalFormationPacket chi M) : Finset P.E :=
  letI := P.decidableEqV
  letI := P.fintypeE
  letI := P.decidableEqE
  formationEdgeBoundary P.tail P.head P.interior

/-- Boundary cardinality of a finite formation packet. -/
def boundaryCard {chi M : ℝ} (P : FiniteLocalFormationPacket chi M) : ℕ :=
  P.boundary.card

/-- Bundled finite-packet formation Cheeger inequality. -/
theorem volume_mul_abs_current_le_boundaryCapacity {chi M : ℝ}
    (P : FiniteLocalFormationPacket chi M) :
    (P.volume : ℝ) * |chi| ≤ (P.boundaryCard : ℝ) * M := by
  letI := P.fintypeV
  letI := P.decidableEqV
  letI := P.fintypeE
  letI := P.decidableEqE
  simpa [volume, boundaryCard, boundary] using
    card_mul_abs_bulkCurrent_le_boundaryCapacity
      P.tail P.head P.interior P.current chi M P.bulk P.edgeBound

/-- **Inverse-isoperimetric positive survivor.** A nonzero bulk current on a nonempty packet forces
one boundary edge to carry at least the average compulsory boundary current. -/
theorem exists_boundary_current_carries_bulk {chi M : ℝ}
    (P : FiniteLocalFormationPacket chi M)
    (hchi : chi ≠ 0) (hvolume : 0 < P.volume) :
    ∃ e ∈ P.boundary,
      (P.volume : ℝ) * |chi| ≤ (P.boundaryCard : ℝ) * |P.current e| := by
  letI := P.fintypeV
  letI := P.decidableEqV
  letI := P.fintypeE
  letI := P.decidableEqE
  have hbulk := card_mul_abs_bulkCurrent_le_cutTraffic
    P.tail P.head P.interior P.current chi P.bulk
  have hboundary : P.boundary.Nonempty := by
    by_contra hempty
    have hempty' : P.boundary = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have htraffic : formationCutTraffic P.tail P.head P.interior P.current = 0 := by
      rw [formationCutTraffic_eq_sum_boundary_abs]
      have hcut : formationEdgeBoundary P.tail P.head P.interior = ∅ := by
        simpa [boundary] using hempty'
      rw [hcut]
      simp
    have hleft : 0 < (P.interior.card : ℝ) * |chi| := by
      positivity
    rw [htraffic] at hbulk
    exact (not_lt_of_ge hbulk) hleft
  obtain ⟨e, he, hmax⟩ :=
    Finset.exists_max_image P.boundary (fun e => |P.current e|) hboundary
  refine ⟨e, he, ?_⟩
  calc
    (P.volume : ℝ) * |chi| ≤ formationCutTraffic P.tail P.head P.interior P.current := by
      simpa [volume] using hbulk
    _ = ∑ b ∈ P.boundary, |P.current b| := by
      simpa [boundary] using
        formationCutTraffic_eq_sum_boundary_abs
          P.tail P.head P.interior P.current
    _ ≤ ∑ _b ∈ P.boundary, |P.current e| :=
      Finset.sum_le_sum fun b hb => hmax b hb
    _ = (P.boundaryCard : ℝ) * |P.current e| := by
      simp [boundaryCard]

end FiniteLocalFormationPacket

/-- **Formation Følner selection.** A family whose edge-capacity-weighted boundary becomes
arbitrarily small relative to bulk volume has zero bulk character. -/
theorem bulkCurrent_eq_zero_of_weightedFormationFolner
    {ι : Type*} (chi M : ℝ) (P : ι → FiniteLocalFormationPacket chi M)
    (hfolner : ∀ ε : ℝ, 0 < ε → ∃ i : ι,
      (P i).boundaryCard * M < ε * (P i).volume) :
    chi = 0 := by
  by_contra hchi
  have habs : 0 < |chi| := abs_pos.mpr hchi
  obtain ⟨i, hi⟩ := hfolner |chi| habs
  have hcapacity := (P i).volume_mul_abs_current_le_boundaryCapacity
  have : (P i).volume * |chi| < |chi| * (P i).volume := hcapacity.trans_lt hi
  rw [mul_comm] at this
  exact (lt_irrefl _) this

/-- A rank-`d`, width-`w` box with codimension-one boundary capacity obeys the rank-width current
bound `w * |chi| ≤ 2 * M * d`. -/
theorem boxRankWidth_current_le
    (chi M w : ℝ) (d : ℕ) (hw : 0 < w) (hd : 0 < d)
    (hcurrent : w ^ d * |chi| ≤ 2 * M * (d : ℝ) * w ^ (d - 1)) :
    w * |chi| ≤ 2 * M * (d : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hpow : 0 < w ^ k := pow_pos hw k
  have hfactor :
      w ^ k * (w * |chi|) ≤ w ^ k * (2 * M * ((k + 1 : ℕ) : ℝ)) := by
    calc
      w ^ k * (w * |chi|) = w ^ (k + 1) * |chi| := by ring
      _ ≤ 2 * M * ((k + 1 : ℕ) : ℝ) * w ^ ((k + 1) - 1) := hcurrent
      _ = w ^ k * (2 * M * ((k + 1 : ℕ) : ℝ)) := by simp; ring
  exact le_of_mul_le_mul_left hfactor hpow

/-- **Sublinear rank-width selection.** If channel rank is asymptotically negligible relative to
legal packet width under fixed local capacity, the bulk character vanishes. -/
theorem bulkCurrent_eq_zero_of_sublinearRankWidth
    {ι : Type*} (chi M : ℝ) (w : ι → ℝ) (d : ι → ℕ)
    (hw : ∀ i, 0 < w i) (hd : ∀ i, 0 < d i)
    (hcurrent : ∀ i,
      w i ^ d i * |chi| ≤ 2 * M * (d i : ℝ) * w i ^ (d i - 1))
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ i : ι,
      2 * M * (d i : ℝ) < ε * w i) :
    chi = 0 := by
  by_contra hchi
  have habs : 0 < |chi| := abs_pos.mpr hchi
  obtain ⟨i, hi⟩ := hthin |chi| habs
  have hbound := boxRankWidth_current_le chi M (w i) (d i) (hw i) (hd i) (hcurrent i)
  exact (not_lt_of_ge hbound) (by simpa [mul_comm] using hi)

/-- Positive survivor of the box law: nonzero current forces positive channel-rank density unless
local edge capacity diverges. -/
theorem abs_current_div_capacity_le_rank_div_width
    (chi M w : ℝ) (d : ℕ) (hM : 0 < M) (hw : 0 < w)
    (hbound : w * |chi| ≤ 2 * M * (d : ℝ)) :
    |chi| / (2 * M) ≤ (d : ℝ) / w := by
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hM) hw]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hbound

namespace FiniteLocalFormationPacket

/-- Packet specialization of the rank-width law from exact bulk volume and a box boundary-port
count. -/
theorem boxRankWidth_current_le {chi M : ℝ}
    (P : FiniteLocalFormationPacket chi M) (w : ℝ) (d : ℕ)
    (hw : 0 < w) (hd : 0 < d) (hM : 0 ≤ M)
    (hvolume : (P.volume : ℝ) = w ^ d)
    (hboundary : (P.boundaryCard : ℝ) ≤ 2 * (d : ℝ) * w ^ (d - 1)) :
    w * |chi| ≤ 2 * M * (d : ℝ) := by
  have hcapacity := P.volume_mul_abs_current_le_boundaryCapacity
  have hcurrent : w ^ d * |chi| ≤ 2 * M * (d : ℝ) * w ^ (d - 1) := by
    calc
      w ^ d * |chi| = (P.volume : ℝ) * |chi| := by rw [hvolume]
      _ ≤ (P.boundaryCard : ℝ) * M := hcapacity
      _ ≤ (2 * (d : ℝ) * w ^ (d - 1)) * M :=
        mul_le_mul_of_nonneg_right hboundary hM
      _ = 2 * M * (d : ℝ) * w ^ (d - 1) := by ring
  exact GaloisForLFunctions.HTGeometry.boxRankWidth_current_le
    chi M w d hw hd hcurrent

end FiniteLocalFormationPacket

end GaloisForLFunctions.HTGeometry
