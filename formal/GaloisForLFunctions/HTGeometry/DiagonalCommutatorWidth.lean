import GaloisForLFunctions.HTGeometry.FoldedPhaseGenerator
import GaloisForLFunctions.HTGeometry.IncidenceLeakageDimensionLoss

/-!
# Commutators against a diagonal are bounded by the spectral width

The commutator of a diagonal matrix with anything is the entrywise product by the energy
differences, so its Hilbert--Schmidt energy is at most the squared spectral width times the energy of
the operand.  No operator-norm theory and no centring are needed: the bound is exact entry by entry,
and the constant is the width itself rather than twice the radius.

Combined with a tangent lower bound on the commutator, this converts a distance-to-the-line estimate
into a distance-to-the-shell estimate by one triangle inequality.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

section Commutator

open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutator against a diagonal is the entrywise product by the energy differences. -/
theorem commutator_diagonal_apply (E : n → ℝ) (X : Matrix n n ℂ) (i j : n) :
    (Matrix.diagonal (fun l => ((E l : ℝ) : ℂ)) * X
      - X * Matrix.diagonal (fun l => ((E l : ℝ) : ℂ))) i j
      = ((E i - E j : ℝ) : ℂ) * X i j := by
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast
  ring

/-- **The Hilbert--Schmidt commutator bound.**  The commutator against a diagonal has energy at most
the squared spectral width times the energy of the operand. -/
theorem hsSqRe_commutator_diagonal_le (E : n → ℝ) (X : Matrix n n ℂ) {W : ℝ}
    (hW : ∀ i j, |E i - E j| ≤ W) :
    hsSqRe (Matrix.diagonal (fun l => ((E l : ℝ) : ℂ)) * X
      - X * Matrix.diagonal (fun l => ((E l : ℝ) : ℂ)))
      ≤ W ^ 2 * hsSqRe X := by
  rw [hsSqRe_eq_sum, hsSqRe_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [commutator_diagonal_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hab := hW b a
  have hnn : (0 : ℝ) ≤ |E b - E a| := abs_nonneg _
  have hsq : |E b - E a| ^ 2 ≤ W ^ 2 := by nlinarith [hab, hnn]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

end Commutator

/-! ## The spectral width -/

section Width

variable {n : Type*} [Fintype n]

/-- Every energy difference is bounded by the spectral width. -/
theorem abs_sub_le_width (hne : (Finset.univ : Finset n).Nonempty) (E : n → ℝ) (i j : n) :
    |E i - E j| ≤ (Finset.univ.sup' hne E) - (Finset.univ.inf' hne E) := by
  have hi := Finset.le_sup' E (Finset.mem_univ i)
  have hj := Finset.le_sup' E (Finset.mem_univ j)
  have hi' := Finset.inf'_le E (Finset.mem_univ i)
  have hj' := Finset.inf'_le E (Finset.mem_univ j)
  rw [abs_le]
  constructor <;> linarith

end Width

/-! ## From a tangent bound to a distance bound -/

/-- **`(26)`: the triangle step.**  If a candidate is close to the line in proportion to its distance
from the target, the target is close to the line in proportion to its distance from the candidate. -/
theorem infDist_le_of_tangent {V : Type*} [NormedAddCommGroup V] {S : Set V} {F K : V} {r : ℝ}
    (h : Metric.infDist K S ≤ r * ‖K - F‖) :
    Metric.infDist F S ≤ (1 + r) * ‖F - K‖ := by
  have htri : Metric.infDist F S ≤ Metric.infDist K S + dist F K :=
    Metric.infDist_le_infDist_add_dist
  have hdist : dist F K = ‖F - K‖ := dist_eq_norm F K
  have hsym : ‖K - F‖ = ‖F - K‖ := norm_sub_rev K F
  rw [hdist] at htri
  rw [hsym] at h
  linarith [htri, h]

/-! ## The tangent gap and distance to a subspace -/

section Tangent

/-- **`(21)` homogenized.**  A gap on the unit sphere is a gap everywhere, for any homogeneous
map. -/
theorem gap_mul_norm_le {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : V → W)
    (hT : ∀ (c : ℝ) (v : V), T (c • v) = c • T v) {γ : ℝ}
    (hgap : ∀ v : V, ‖v‖ = 1 → γ ≤ ‖T v‖) (v : V) :
    γ * ‖v‖ ≤ ‖T v‖ := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    have hzero : T 0 = 0 := by
      have h := hT 0 0
      simpa using h
    simp [hzero]
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunit : ‖(‖v‖)⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
      field_simp
    have h := hgap _ hunit
    rw [hT] at h
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos] at h
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    calc γ * ‖v‖ ≤ ‖v‖⁻¹ * ‖T v‖ * ‖v‖ := hmul
      _ = ‖T v‖ := by field_simp

end Tangent

/-! ## Distance to a subspace -/

section Distance

variable {V : Type*} [NormedAddCommGroup V]

/-- Distance to a subgroup is invariant under translation by the subgroup. -/
theorem infDist_add_mem (S : AddSubgroup V) (x v : V) (hv : v ∈ S) :
    Metric.infDist (x + v) (S : Set V) = Metric.infDist x (S : Set V) := by
  have hne : (S : Set V).Nonempty := ⟨0, S.zero_mem⟩
  have key : ∀ (y w : V), w ∈ S →
      Metric.infDist (y + w) (S : Set V) ≤ Metric.infDist y (S : Set V) := by
    intro y w hw
    refine (Metric.le_infDist hne).mpr fun s hs => ?_
    calc Metric.infDist (y + w) (S : Set V) ≤ dist (y + w) (s + w) :=
          Metric.infDist_le_dist_of_mem (S.add_mem hs hw)
      _ = dist y s := by simp [dist_eq_norm]
  refine le_antisymm (key x v hv) ?_
  have h2 := key (x + v) (-v) (S.neg_mem hv)
  simpa using h2

end Distance


section SubmoduleDistance

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem infDist_add_mem_submodule (S : Submodule ℝ V) (x v : V) (hv : v ∈ S) :
    Metric.infDist (x + v) (S : Set V) = Metric.infDist x (S : Set V) :=
  infDist_add_mem S.toAddSubgroup x v hv

/-- Distance to a subspace is absolutely homogeneous. -/
theorem infDist_smul_submodule (S : Submodule ℝ V) (c : ℝ) (x : V) :
    Metric.infDist (c • x) (S : Set V) = |c| * Metric.infDist x (S : Set V) := by
  have hne : (S : Set V).Nonempty := ⟨0, S.zero_mem⟩
  have half : ∀ (d : ℝ) (y : V), d ≠ 0 →
      Metric.infDist (d • y) (S : Set V) ≤ |d| * Metric.infDist y (S : Set V) := by
    intro d y hd
    have hdpos : 0 < |d| := abs_pos.mpr hd
    have hkey : ∀ s ∈ (S : Set V),
        Metric.infDist (d • y) (S : Set V) / |d| ≤ dist y s := by
      intro s hs
      have hmem : d • s ∈ (S : Set V) := S.smul_mem d hs
      have hle : Metric.infDist (d • y) (S : Set V) ≤ dist (d • y) (d • s) :=
        Metric.infDist_le_dist_of_mem hmem
      have heq : dist (d • y) (d • s) = |d| * dist y s := by
        rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
      rw [heq] at hle
      rw [div_le_iff₀ hdpos]
      linarith [hle]
    have h := (Metric.le_infDist hne).mpr hkey
    rw [div_le_iff₀ hdpos] at h
    linarith [h]
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    simp [Metric.infDist_zero_of_mem S.zero_mem]
  · refine le_antisymm (half c x hc) ?_
    have hinv : c⁻¹ ≠ 0 := inv_ne_zero hc
    have h2 := half c⁻¹ (c • x) hinv
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
    have hcpos : 0 < |c| := abs_pos.mpr hc
    have habs : |c⁻¹| = |c|⁻¹ := abs_inv c
    rw [habs] at h2
    have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt hcpos)
    calc |c| * Metric.infDist x (S : Set V)
        ≤ |c| * (|c|⁻¹ * Metric.infDist (c • x) (S : Set V)) := hmul
      _ = Metric.infDist (c • x) (S : Set V) := by field_simp

/-- **`(27)`: folding by a physical multiple rescales the distance to the centralizer line.** -/
theorem infDist_folded (S : Submodule ℝ V) {p : V} (hp : p ∈ S) (N : V) (c : ℝ) :
    Metric.infDist (p - c • N) (S : Set V) = |c| * Metric.infDist N (S : Set V) := by
  have hrw : p - c • N = (-c) • N + p := by
    rw [neg_smul]
    abel
  rw [hrw, infDist_add_mem_submodule S _ p hp, infDist_smul_submodule, abs_neg]

end SubmoduleDistance


end GaloisForLFunctions.HTGeometry
