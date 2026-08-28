import GaloisForLFunctions.HTGeometry.CyclicPhaseFiniteUnion
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing

/-!
# Continuous cyclic phase exclusion

The cyclic-frequency phase curve has a dimension-free speed after target normalization.  A fixed
mesh of spacing `1/256` therefore turns simultaneous mesh avoidance into robust avoidance at every
real time in the return-excised interval.  Unlike the earlier torsion-polygon argument, this result
does not leave interpolation gaps between integer vertices.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [Fintype I]

lemma cyclicPhaseValue_eq_exp (p : ℕ) (t : ℝ) (q : Fin p) :
    cyclicPhaseValue p t q =
      Complex.exp ((((q.val : ℝ) * (2 * Real.pi * t / p) : ℝ) : ℂ) * Complex.I) := by
  rw [cyclicPhaseValue, cyclicPhaseRatio, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Every cyclic coordinate moves at speed strictly below `2π` over one normalized period. -/
lemma norm_cyclicPhaseValue_sub_le {p : ℕ} (hp : 0 < p) (q : Fin p) (t s : ℝ) :
    ‖cyclicPhaseValue p t q - cyclicPhaseValue p s q‖ ≤
      2 * Real.pi * |t - s| := by
  rw [cyclicPhaseValue_eq_exp, cyclicPhaseValue_eq_exp]
  refine le_trans (norm_exp_ofReal_mul_I_sub_le
    ((q.val : ℝ) * (2 * Real.pi * t / p))
    ((q.val : ℝ) * (2 * Real.pi * s / p))) ?_
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hq : (q.val : ℝ) ≤ p := by
    exact_mod_cast (Nat.le_of_lt q.isLt)
  rw [show (q.val : ℝ) * (2 * Real.pi * t / p) -
      (q.val : ℝ) * (2 * Real.pi * s / p) =
      ((q.val : ℝ) / p) * (2 * Real.pi) * (t - s) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg (by positivity) hpR.le),
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hratio : (q.val : ℝ) / p ≤ 1 := (div_le_one hpR).mpr hq
  have hratio' :=
    mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 2 * Real.pi)
  rw [one_mul] at hratio'
  exact mul_le_mul_of_nonneg_right hratio' (abs_nonneg _)

/-- Weighted overlaps inherit the exact `ℓ¹` coefficient speed. -/
lemma norm_cyclicOverlap_sub_le {p : ℕ} (hp : 0 < p) (w : I → ℂ)
    (q : I → Fin p) (t s : ℝ) :
    ‖(∑ i, w i * cyclicPhaseValue p t (q i)) -
        ∑ i, w i * cyclicPhaseValue p s (q i)‖ ≤
      2 * Real.pi * |t - s| * ∑ i, ‖w i‖ := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  calc
    ∑ i, ‖w i * cyclicPhaseValue p t (q i) -
        w i * cyclicPhaseValue p s (q i)‖
        = ∑ i, ‖w i‖ * ‖cyclicPhaseValue p t (q i) -
            cyclicPhaseValue p s (q i)‖ := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [← mul_sub, norm_mul]
    _ ≤ ∑ i, ‖w i‖ * (2 * Real.pi * |t - s|) := by
          exact Finset.sum_le_sum fun i _hi =>
            mul_le_mul_of_nonneg_left (norm_cyclicPhaseValue_sub_le hp (q i) t s)
              (norm_nonneg _)
    _ = 2 * Real.pi * |t - s| * ∑ i, ‖w i‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ring

lemma abs_norm_cyclicOverlap_sub_le {p : ℕ} (hp : 0 < p) (w : I → ℂ)
    (q : I → Fin p) (t s : ℝ) :
    |‖∑ i, w i * cyclicPhaseValue p t (q i)‖ -
        ‖∑ i, w i * cyclicPhaseValue p s (q i)‖| ≤
      2 * Real.pi * |t - s| * ∑ i, ‖w i‖ := by
  exact (abs_norm_sub_norm_le _ _).trans (norm_cyclicOverlap_sub_le hp w q t s)

lemma returnExcised_plateauGridCount_eq {p : ℕ} (hp8 : 8 ≤ p) :
    plateauGridCount ((p : ℝ) - 8) (1 / 256) = 256 * (p - 8) + 1 := by
  have hcast : ((p : ℝ) - 8) / (1 / 256) = (256 * (p - 8) : ℕ) := by
    push_cast
    rw [Nat.cast_sub hp8]
    norm_num
    ring
  rw [plateauGridCount, hcast, Nat.ceil_natCast]

/-- Exact finite grid for the period with four laboratory-time units removed at each return. -/
abbrev cyclicReturnExcisedMesh (p : ℕ) := Fin (256 * (p - 8) + 1)

def cyclicReturnExcisedMeshTime (p : ℕ) (k : cyclicReturnExcisedMesh p) : ℝ :=
  4 + (k.val : ℝ) / 256

lemma cyclicReturnExcisedMeshTime_mem {p : ℕ} (hp8 : 8 ≤ p)
    (k : cyclicReturnExcisedMesh p) :
    cyclicReturnExcisedMeshTime p k ∈ Set.Icc (4 : ℝ) ((p : ℝ) - 4) := by
  constructor
  · rw [cyclicReturnExcisedMeshTime]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by norm_num))
  · have hk : k.val ≤ 256 * (p - 8) := by omega
    have hkR : (k.val : ℝ) ≤ 256 * (p - 8) := by exact_mod_cast hk
    have hcast : ((p - 8 : ℕ) : ℝ) = (p : ℝ) - 8 := by
      rw [Nat.cast_sub hp8]
      norm_num
    rw [cyclicReturnExcisedMeshTime]
    linarith

/-- Every return-excised time lies within `1/256` of a grid point that is itself return-excised. -/
lemma exists_cyclicReturnExcisedMeshTime_near {p : ℕ} (hp8 : 8 ≤ p) {t : ℝ}
    (ht : t ∈ Set.Icc (4 : ℝ) ((p : ℝ) - 4)) :
    ∃ k : cyclicReturnExcisedMesh p,
      |t - cyclicReturnExcisedMeshTime p k| ≤ 1 / 256 := by
  have ht' : t ∈ Set.Icc (4 : ℝ) (4 + ((p : ℝ) - 8)) := by
    convert ht using 1 <;> ring
  obtain ⟨j, hj⟩ := exists_plateauGrid_near (W := (p : ℝ) - 8)
    (mesh := 1 / 256) (by norm_num) 4 ht'
  let k : cyclicReturnExcisedMesh p :=
    Fin.cast (returnExcised_plateauGridCount_eq hp8) j
  exact ⟨k, by
    simpa [k, cyclicReturnExcisedMeshTime, plateauGridPoint, div_eq_mul_inv] using hj⟩

variable {Y : Type*} [Fintype Y]

/-- **Continuous return-excised same-draw avoidance.**  If target coefficient vectors have a
common squared mass `energy`, have `ℓ¹` mass at most one, and their complete mesh entropy fits
inside the explicit cyclic cap exponent, then one frequency draw stays at overlap below `4/5`
from every target at every real time from the end of the four-unit ramp until four units before
the exact cyclic return. -/
theorem exists_cyclicFrequencies_continuous_returnExcised_avoid
    (p : ℕ) (hp8 : 8 ≤ p) (weight : Y → I → ℂ) {energy : ℝ}
    (henergy : 0 < energy)
    (hweight : ∀ y, (↑(∑ i, ‖weight y i‖₊ ^ 2) : ℝ) ≤ energy)
    (hl1 : ∀ y, ∑ i, ‖weight y i‖ ≤ 1)
    (hbudget : ((256 * (p - 8) + 1 : ℕ) : ℝ) * Fintype.card Y *
        (4 * Real.exp (-((3 / 4 : ℝ) - 1 / 8) ^ 2 / (16 * energy))) < 1) :
    ∃ q : I → Fin p, ∀ t ∈ Set.Icc (4 : ℝ) ((p : ℝ) - 4), ∀ y,
      ‖∑ i, weight y i * cyclicPhaseValue p t (q i)‖ < 4 / 5 := by
  classical
  have hp : 0 < p := by omega
  letI : NeZero p := ⟨hp.ne'⟩
  have hmean : ∀ (k : cyclicReturnExcisedMesh p) y,
      ‖cyclicPhaseMean p (cyclicReturnExcisedMeshTime p k) * ∑ i, weight y i‖ ≤
        (1 / 8 : ℝ) := by
    intro k y
    have htime := cyclicReturnExcisedMeshTime_mem hp8 k
    have hdir := eight_mul_norm_cyclicPhaseMean_le_one_of_returnExcised hp
      htime.1 htime.2
    have hdir' : ‖cyclicPhaseMean p (cyclicReturnExcisedMeshTime p k)‖ ≤
        (1 / 8 : ℝ) := by
      nlinarith [norm_nonneg (cyclicPhaseMean p (cyclicReturnExcisedMeshTime p k))]
    have hsum : ‖∑ i, weight y i‖ ≤ ∑ i, ‖weight y i‖ := norm_sum_le _ _
    have hsum1 : ‖∑ i, weight y i‖ ≤ 1 := hsum.trans (hl1 y)
    rw [norm_mul]
    calc
      ‖cyclicPhaseMean p (cyclicReturnExcisedMeshTime p k)‖ * ‖∑ i, weight y i‖
          ≤ (1 / 8 : ℝ) * 1 :=
        mul_le_mul hdir' hsum1 (norm_nonneg _) (by norm_num)
      _ = 1 / 8 := by norm_num
  have hbudget' :
      ((Fintype.card (cyclicReturnExcisedMesh p) : ℝ) * Fintype.card Y) *
        (4 * Real.exp (-((3 / 4 : ℝ) - 1 / 8) ^ 2 / (16 * energy))) < 1 := by
    simpa [cyclicReturnExcisedMesh] using hbudget
  obtain ⟨q, hq⟩ := exists_cyclicFrequencies_avoid_finite_time_target_union_of_energy_le
    p hp (cyclicReturnExcisedMeshTime p) weight
      (threshold := (3 / 4 : ℝ)) (bias := (1 / 8 : ℝ)) (energy := energy)
      henergy (by norm_num) (by norm_num) hweight hmean hbudget'
  refine ⟨q, ?_⟩
  intro t ht y
  obtain ⟨k, hknear⟩ := exists_cyclicReturnExcisedMeshTime_near hp8 ht
  have hk := hq k y
  have hlip := abs_norm_cyclicOverlap_sub_le hp (weight y) q t
    (cyclicReturnExcisedMeshTime p k)
  have hspeed :
      2 * Real.pi * |t - cyclicReturnExcisedMeshTime p k| * ∑ i, ‖weight y i‖ <
        (1 / 32 : ℝ) := by
    have hfirst :
        2 * Real.pi * |t - cyclicReturnExcisedMeshTime p k| ≤
          2 * Real.pi * (1 / 256 : ℝ) :=
      mul_le_mul_of_nonneg_left hknear (by positivity)
    have hsecond :
        2 * Real.pi * |t - cyclicReturnExcisedMeshTime p k| * ∑ i, ‖weight y i‖ ≤
          (2 * Real.pi * (1 / 256 : ℝ)) * 1 :=
      calc
        2 * Real.pi * |t - cyclicReturnExcisedMeshTime p k| * ∑ i, ‖weight y i‖
            ≤ (2 * Real.pi * (1 / 256 : ℝ)) * ∑ i, ‖weight y i‖ :=
          mul_le_mul_of_nonneg_right hfirst (Finset.sum_nonneg fun i _ => norm_nonneg _)
        _ ≤ (2 * Real.pi * (1 / 256 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (hl1 y) (by positivity)
    have hpi : Real.pi < 4 := Real.pi_lt_four
    calc
      2 * Real.pi * |t - cyclicReturnExcisedMeshTime p k| * ∑ i, ‖weight y i‖
          ≤ (2 * Real.pi * (1 / 256 : ℝ)) * 1 := hsecond
      _ < (1 / 32 : ℝ) := by nlinarith
  have hdiff :
      |‖∑ i, weight y i * cyclicPhaseValue p t (q i)‖ -
          ‖∑ i, weight y i *
            cyclicPhaseValue p (cyclicReturnExcisedMeshTime p k) (q i)‖| <
        (1 / 32 : ℝ) := hlip.trans_lt hspeed
  have hforward :
      ‖∑ i, weight y i * cyclicPhaseValue p t (q i)‖ -
          ‖∑ i, weight y i *
            cyclicPhaseValue p (cyclicReturnExcisedMeshTime p k) (q i)‖ <
        (1 / 32 : ℝ) := (le_abs_self _).trans_lt hdiff
  norm_num at hk ⊢
  linarith

end

end GaloisForLFunctions.HTGeometry
