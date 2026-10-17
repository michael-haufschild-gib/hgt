import GaloisForLFunctions.BiScaleUncertainty.IntegerBlockCoisometry
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Convergent infinite block variance

Finite pair squares measure the exact loss in block aggregation. Regrouping
the actual ℓ² square series proves convergence and its value for every input.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def finiteBlockVariance (m : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range m, ∑ s ∈ Finset.range r, (u r-u s)^2

theorem finiteBlockVariance_nonneg (m : ℕ) (u : ℕ → ℝ) :
    0 ≤ finiteBlockVariance m u :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem finiteBlockVariance_eq (m : ℕ) (u : ℕ → ℝ) :
    finiteBlockVariance m u = (m : ℝ)*(∑ r ∈ Finset.range m, (u r)^2)-
      (∑ r ∈ Finset.range m, u r)^2 := by
  induction m with
  | zero => simp [finiteBlockVariance]
  | succ m ih =>
      have he : (∑ s ∈ Finset.range m, (u m-u s)^2) =
          (m : ℝ)*(u m)^2-2*u m*(∑ s ∈ Finset.range m, u s)+
            ∑ s ∈ Finset.range m, (u s)^2 := by
        simp_rw [show ∀ s, (u m-u s)^2 = (u m)^2-(2*u m)*u s+(u s)^2 by
          intro s; ring]
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [finiteBlockVariance] at ih
      simp only [finiteBlockVariance, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      rw [ih, he]
      ring

theorem finiteBlockVariance_zero_iff (m : ℕ) (u : ℕ → ℝ) :
    finiteBlockVariance m u = 0 ↔ ∀ r, r < m → ∀ s, s < m → u r = u s := by
  rw [finiteBlockVariance, Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  constructor
  · intro h r hr s hs
    have hp (i j : ℕ) (hi : i < m) (hj : j < i) : u i = u j := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k (_hk : k ∈ Finset.range i) =>
        sq_nonneg (u i-u k))).mp (h i (Finset.mem_range.mpr hi)) j (Finset.mem_range.mpr hj)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    rcases lt_trichotomy r s with hrs | hrs | hrs
    · exact (hp s r hs hrs).symm
    · rw [hrs]
    · exact hp r s hr hrs
  · intro h r hr
    apply Finset.sum_eq_zero
    intro s hs
    rw [h r (Finset.mem_range.mp hr) s
      ((Finset.mem_range.mp hs).trans (Finset.mem_range.mp hr)), sub_self, zero_pow (by decide)]

def integerBlockVariance (m : ℕ) (w : TraceData) (j : ℕ) : ℝ :=
  finiteBlockVariance m (fun r => w (m*j+r))

theorem integerBlockVariance_nonneg (m : ℕ) (w : TraceData) (j : ℕ) :
    0 ≤ integerBlockVariance m w j := finiteBlockVariance_nonneg _ _

theorem hasSum_integerBlock_squares (m : ℕ) (hm : 0 < m) (w : TraceData) :
    HasSum (fun j => ∑ k ∈ Finset.Ico (m*j) (m*(j+1)), (w k)^2) (‖w‖^2) := by
  have hs : Summable (fun k => (w k)^2) := by
    simpa only [Real.inner_apply, pow_two] using lp.summable_inner (𝕜 := ℝ) w w
  have ht := hs.hasSum.tsum_fiberwise (fun k => k/m)
  rw [← norm_sq_traceData] at ht
  apply ht.congr_fun
  intro j
  have he : (fun k => k/m) ⁻¹' {j} = (Finset.Ico (m*j) (m*(j+1)) : Set ℕ) := by
    ext k
    exact (mem_integerBlock_iff m j k hm).symm
  rw [he]
  exact (Finset.tsum_subtype' _ (fun k => (w k)^2)).symm

theorem hasSum_integerBlockVariance (m : ℕ) (w : TraceData) :
    HasSum (integerBlockVariance m w) ((m : ℝ)*‖w‖^2-‖integerBlockSum m w‖^2) := by
  by_cases hm : m = 0
  · subst m
    have hz : integerBlockVariance 0 w = fun _ => 0 := by
      funext j
      simp [integerBlockVariance, finiteBlockVariance]
    rw [hz, integerBlockSum_zero]
    simp
  · have hb : HasSum (fun j => (integerBlockSum m w j)^2) (‖integerBlockSum m w‖^2) := by
      rw [norm_sq_traceData]
      apply Summable.hasSum
      simpa only [Real.inner_apply, pow_two] using
        lp.summable_inner (𝕜 := ℝ) (integerBlockSum m w) (integerBlockSum m w)
    have h := ((hasSum_integerBlock_squares m (Nat.pos_of_ne_zero hm) w).mul_left (m : ℝ)).sub hb
    apply h.congr_fun
    intro j
    rw [integerBlockVariance, finiteBlockVariance_eq, integerBlockSum_range,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel_left]

theorem summable_integerBlockVariance (m : ℕ) (w : TraceData) :
    Summable (integerBlockVariance m w) := (hasSum_integerBlockVariance m w).summable

theorem integerBlockVariance_tsum (m : ℕ) (w : TraceData) :
    ∑' j, integerBlockVariance m w j = (m : ℝ)*‖w‖^2-‖integerBlockSum m w‖^2 :=
  (hasSum_integerBlockVariance m w).tsum_eq

theorem integerBlockVariance_residual (m : ℕ) (w : TraceData) :
    ∑' j, integerBlockVariance m w j = (m : ℝ)*‖w-integerBlockMean m w‖^2 := by
  rw [integerBlockVariance_tsum, integerBlockMean_defect]

def IntegerBlockConstant (m : ℕ) (w : TraceData) : Prop :=
  ∀ j r, r < m → ∀ s, s < m → w (m*j+r) = w (m*j+s)

theorem integerBlockSum_energy_eq_iff (m : ℕ) (w : TraceData) :
    ‖integerBlockSum m w‖^2 = (m : ℝ)*‖w‖^2 ↔ IntegerBlockConstant m w := by
  constructor
  · intro h j r hr s hs
    have hz : ∑' j, integerBlockVariance m w j = 0 := by
      rw [integerBlockVariance_tsum, h, sub_self]
    have hj : integerBlockVariance m w j = 0 := by
      apply le_antisymm _ (integerBlockVariance_nonneg m w j)
      simpa only [hz] using (summable_integerBlockVariance m w).le_tsum j
        (fun k _ => integerBlockVariance_nonneg m w k)
    exact (finiteBlockVariance_zero_iff _ _).mp hj r hr s hs
  · intro h
    have hz (j : ℕ) : integerBlockVariance m w j = 0 :=
      (finiteBlockVariance_zero_iff _ _).mpr (h j)
    have he := integerBlockVariance_tsum m w
    simp only [hz, tsum_zero] at he
    linarith only [he]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
