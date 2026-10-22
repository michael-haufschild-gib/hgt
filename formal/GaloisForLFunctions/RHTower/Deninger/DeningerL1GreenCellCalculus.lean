import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Local original Green primitives and the complete two-ended boundary

The translates of an integrable source form an absolutely summable family
in L1 on the original cell `(0,L]`. Their future sum is a local primitive
of `1 - translation_L`. Its positive cell translates tend to zero and its
negative cell translates tend to the full periodization of the same source.
The original cell measure and Fourier normalization are retained.

Every cellwise L1 primitive of the same equation differs from this one by
a cell value independent of the integer translate. Its two endpoint limits
are therefore `c` and `P+c`, without any endpoint assumption. The complete
jump is always `P`, with the original Fourier coefficients of the source.
-/

open MeasureTheory Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem originalCell_norm_hasSum {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) :
    HasSum (fun k : ℤ => ∫ t in Set.Ioc 0 L, ‖f (t + k * L)‖)
      (∫ t, ‖f t‖) := by
  have hs := ((hf.comp_mul_left' hL.ne').norm).hasSum_intervalIntegral_comp_add_int
  have hc (k : ℤ) :
      L * (∫ t in (0:ℝ)..1, ‖f (L * (t + k))‖) =
        ∫ t in Set.Ioc 0 L, ‖f (t + k * L)‖ := by
    calc
      _ = L • (∫ t in (0:ℝ)..1, (fun x => ‖f (x + k * L)‖) (L*t)) := by
        simp only [smul_eq_mul, mul_add, mul_comm L (k : ℝ)]
      _ = ∫ t in L * 0..L * 1, ‖f (t + k * L)‖ :=
        intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
          (fun x : ℝ => ‖f (x + (k : ℝ) * L)‖) L
      _ = _ := by simp only [mul_zero, mul_one, intervalIntegral.integral_of_le hL.le]
  have hg : L * (∫ t, ‖f (L*t)‖) = ∫ t, ‖f t‖ := by
    rw [Measure.integral_comp_mul_left (fun t => ‖f t‖) L]
    simp [abs_of_pos (inv_pos.mpr hL), smul_eq_mul, hL.ne']
  simpa only [hc, hg] using hs.mul_left L

/-- L1 on the original cell with unnormalized Lebesgue measure. -/
abbrev DeningerOriginalCellL1 (L : ℝ) := Lp ℂ 1 (volume.restrict (Set.Ioc 0 L))

/-- An integer translate of the actual source, restricted to its original cell. -/
def deningerOriginalSourceCell {f : ℝ → ℂ} (hf : Integrable f) (L : ℝ)
    (k : ℤ) : DeningerOriginalCellL1 L :=
  ((hf.comp_add_right ((k : ℝ)*L)).restrict).toL1 (fun t => f (t+k*L))

private theorem sourceCell_norm_summable {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) : Summable (fun k : ℤ => ‖deningerOriginalSourceCell hf L k‖) := by
  simpa only [deningerOriginalSourceCell, L1.norm_of_fun_eq_integral_norm]
    using (originalCell_norm_hasSum hf hL).summable

private def futureCell {E : Type*} [NormedAddCommGroup E] (v : ℤ → E) (m : ℤ) : E :=
  ∑' j : ℕ, v (m+j)

private theorem futureCell_summable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {v : ℤ → E} (hv : Summable v) (m : ℤ) : Summable (fun j : ℕ => v (m+j)) := by
  apply hv.comp_injective
  intro i j hij
  exact_mod_cast add_left_cancel hij

private theorem pastCell_summable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {v : ℤ → E} (hv : Summable v) (m : ℤ) : Summable (fun j : ℕ => v (m-(j+1))) := by
  apply hv.comp_injective (i := fun j : ℕ => m - ((j : ℤ)+1))
  intro i j hij
  change m - ((i : ℤ)+1) = m - ((j : ℤ)+1) at hij
  have : (i : ℤ) = j := by omega
  exact_mod_cast this

private theorem futureCell_resolves {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {v : ℤ → E} (hv : Summable v) (m : ℤ) :
    futureCell v m - futureCell v (m+1) = v m := by
  have h := (futureCell_summable hv m).tsum_eq_zero_add
  have he : (∑' j : ℕ, v (m + ((j+1 : ℕ) : ℤ))) = futureCell v (m+1) := by
    apply tsum_congr
    intro j
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    omega
  simpa only [Nat.cast_zero, add_zero, he, futureCell, add_sub_cancel_right] using
    congrArg (fun x => x - futureCell v (m+1)) h

private theorem futureCell_split {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {v : ℤ → E} (hv : Summable v) (m : ℤ) :
    (∑' k : ℤ, v k) = futureCell v m + ∑' j : ℕ, v (m-(j+1)) := by
  let e : ℤ ≃ ℤ := Equiv.addLeft m
  rw [← e.tsum_eq v]
  exact tsum_of_nat_of_neg_add_one (futureCell_summable hv m)
    (by
      change Summable (fun n : ℕ => v (m + -((n : ℤ)+1)))
      simpa only [sub_eq_add_neg] using pastCell_summable hv m)

private theorem futureCell_positive_end {E : Type*} [NormedAddCommGroup E]
    (v : ℤ → E) : Tendsto (fun n : ℕ => futureCell v n) atTop (𝓝 0) := by
  simpa only [futureCell, Nat.cast_add, add_comm] using
    tendsto_sum_nat_add (fun j : ℕ => v j)

private theorem futureCell_negative_end {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {v : ℤ → E} (hv : Summable v) :
    Tendsto (fun n : ℕ => futureCell v (-n)) atTop (𝓝 (∑' k : ℤ, v k)) := by
  have ht : Tendsto (fun n : ℕ => ∑' j : ℕ, v (- (n : ℤ) - (j+1))) atTop (𝓝 0) := by
    convert tendsto_sum_nat_add (fun j : ℕ => v (-((j : ℤ)+1))) using 1
    funext n
    apply tsum_congr
    intro j
    congr 1
    simp only [Nat.cast_add]
    omega
  have he (n : ℕ) : (∑' k : ℤ, v k) - (∑' j : ℕ, v (-(n : ℤ)-(j+1))) =
      futureCell v (-n) := by
    rw [futureCell_split hv (-(n : ℤ)), add_sub_cancel_right]
  simpa only [he, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑' k : ℤ, v k) atTop
      (𝓝 (∑' k : ℤ, v k))).sub ht

/-- Literal future sum of an L1 source; local convergence is proved below. -/
def deningerL1OriginalGreenSum (f : ℝ → ℂ) (L t : ℝ) : ℂ :=
  ∑' j : ℕ, f (t + (j : ℝ)*L)

/-- The original Green primitive viewed on the cell shifted by `m * L`. -/
def deningerL1OriginalGreenCell {f : ℝ → ℂ} (hf : Integrable f) (L : ℝ)
    (m : ℤ) : DeningerOriginalCellL1 L :=
  futureCell (deningerOriginalSourceCell hf L) m

/-- Complete two-ended boundary, in the original cell with its original measure. -/
def deningerL1OriginalBoundaryJump {f : ℝ → ℂ} (hf : Integrable f) (L : ℝ) :
    DeningerOriginalCellL1 L := ∑' k : ℤ, deningerOriginalSourceCell hf L k

private theorem sourceCell_sum_ae {ι : Type*} [Countable ι]
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L)
    (e : ι → ℤ) (he : Function.Injective e) :
    ⇑(∑' j : ι, deningerOriginalSourceCell hf L (e j)) =ᵐ[volume.restrict (Set.Ioc 0 L)]
      (fun t => ∑' j : ι, f (t + (e j : ℝ)*L)) := by
  have hn := (sourceCell_norm_summable hf hL).comp_injective he
  have hfin : (∑' j : ι, ‖deningerOriginalSourceCell hf L (e j)‖ₑ) ≠ (⊤ : ENNReal) := by
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hn
  have hc : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 L),
      ∀ j : ι, deningerOriginalSourceCell hf L (e j) t = f (t + (e j : ℝ)*L) := by
    apply ae_all_iff.mpr
    intro j
    exact Integrable.coeFn_toL1 _
  filter_upwards [Lp.coeFn_tsum hfin, hc] with t ht htc
  exact ht.trans (tsum_congr htc)

/-- The completed cell is the literal original future sum, almost everywhere. -/
theorem deningerL1OriginalGreenCell_ae_eq {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) (m : ℤ) :
    ⇑(deningerL1OriginalGreenCell hf L m) =ᵐ[volume.restrict (Set.Ioc 0 L)]
      (fun t => deningerL1OriginalGreenSum f L (t + (m : ℝ)*L)) := by
  have he : Function.Injective (fun j : ℕ => m + (j : ℤ)) := by
    intro i j hij
    exact_mod_cast add_left_cancel hij
  have h := sourceCell_sum_ae hf hL (fun j : ℕ => m + (j : ℤ)) he
  apply h.trans
  filter_upwards with t
  apply tsum_congr
  intro j
  simp only [Int.cast_add, Int.cast_natCast, add_mul, add_assoc]

/-- The complete boundary is exactly the full periodization of the same source. -/
theorem deningerL1OriginalBoundaryJump_ae_eq {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) :
    ⇑(deningerL1OriginalBoundaryJump hf L) =ᵐ[volume.restrict (Set.Ioc 0 L)]
      l1PeriodizationAtScale f L :=
  sourceCell_sum_ae hf hL (fun k : ℤ => k) Function.injective_id

/-- Literal original orientation: `1 - translation`, without a zero-boundary assumption. -/
theorem deningerL1OriginalGreenCell_resolves {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) (m : ℤ) :
    deningerL1OriginalGreenCell hf L m - deningerL1OriginalGreenCell hf L (m+1) =
      deningerOriginalSourceCell hf L m :=
  futureCell_resolves (sourceCell_norm_summable hf hL).of_norm m

/-- Positive translates have zero L1 limit on the original cell. -/
theorem deningerL1OriginalGreenCell_positive_end {f : ℝ → ℂ} (hf : Integrable f)
    (L : ℝ) : Tendsto (fun n : ℕ => deningerL1OriginalGreenCell hf L n) atTop (𝓝 0) :=
  futureCell_positive_end _

/-- Negative translates retain the full original periodization in L1. -/
theorem deningerL1OriginalGreenCell_negative_end {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n : ℕ => deningerL1OriginalGreenCell hf L (-n)) atTop
      (𝓝 (deningerL1OriginalBoundaryJump hf L)) :=
  futureCell_negative_end (sourceCell_norm_summable hf hL).of_norm

/-- Both ends are retained before taking the limit. -/
theorem deningerL1OriginalGreenCell_complete_jump {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n : ℕ => deningerL1OriginalGreenCell hf L (-n) -
      deningerL1OriginalGreenCell hf L n) atTop
      (𝓝 (deningerL1OriginalBoundaryJump hf L)) := by
  simpa only [sub_zero] using (deningerL1OriginalGreenCell_negative_end hf hL).sub
    (deningerL1OriginalGreenCell_positive_end hf L)

/-- Original cell measure and Fourier normalization survive the two-ended limit. -/
theorem deningerL1OriginalBoundaryJump_coefficient {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) (k : ℤ) :
    fourierCoeffOn hL (deningerL1OriginalBoundaryJump hf L) k =
      (1/L) • 𝓕 f ((1/L)*(k : ℝ)) := by
  rw [congrFun (fourierCoeffOn_congr_ae hL (deningerL1OriginalBoundaryJump_ae_eq hf hL)) k]
  exact fourierCoeffOn_l1PeriodizationAtScale hf hL k

/-- Every original shifted cell admits the literal local primitive in L1. -/
theorem deningerL1OriginalGreenSum_cell_integrable {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) (m : ℤ) :
    IntegrableOn (fun t => deningerL1OriginalGreenSum f L (t + (m : ℝ)*L))
      (Set.Ioc 0 L) :=
  (L1.integrable_coeFn _).congr (deningerL1OriginalGreenCell_ae_eq hf hL m)

/-- The literal locally integrable sum solves the same original source equation on every cell. -/
theorem deningerL1OriginalGreenSum_cell_resolves {f : ℝ → ℂ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) (m : ℤ) :
    (fun t => deningerL1OriginalGreenSum f L (t + (m : ℝ)*L) -
      deningerL1OriginalGreenSum f L (t + (m : ℝ)*L + L)) =ᵐ[volume.restrict (Set.Ioc 0 L)]
      (fun t => f (t + (m : ℝ)*L)) := by
  have hr : ⇑(deningerL1OriginalGreenCell hf L m - deningerL1OriginalGreenCell hf L (m+1))
      =ᵐ[volume.restrict (Set.Ioc 0 L)] (fun t => f (t + (m : ℝ)*L)) := by
    rw [deningerL1OriginalGreenCell_resolves hf hL m]
    exact Integrable.coeFn_toL1 _
  filter_upwards [hr, Lp.coeFn_sub (deningerL1OriginalGreenCell hf L m)
    (deningerL1OriginalGreenCell hf L (m+1)),
    deningerL1OriginalGreenCell_ae_eq hf hL m,
    deningerL1OriginalGreenCell_ae_eq hf hL (m+1)] with t hrt hsub h0 h1
  have ht : t + ((m+1 : ℤ) : ℝ)*L = t + (m : ℝ)*L + L := by push_cast; ring
  rw [hsub, Pi.sub_apply, h0, h1, ht] at hrt
  exact hrt

/-- Any two original primitives differ by an integer-periodic cell value. -/
theorem deningerL1OriginalGreenCell_primitive_classification
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L)
    (u : ℤ → DeningerOriginalCellL1 L)
    (hu : ∀ m, u m - u (m+1) = deningerOriginalSourceCell hf L m) :
    ∃ c : DeningerOriginalCellL1 L,
      ∀ m, u m = deningerL1OriginalGreenCell hf L m + c := by
  let d : ℤ → DeningerOriginalCellL1 L := fun m => u m - deningerL1OriginalGreenCell hf L m
  have hd : Function.Periodic d 1 := by
    intro m
    dsimp [d]
    have h1 := hu m
    have h2 := deningerL1OriginalGreenCell_resolves hf hL m
    have h := h1.trans h2.symm
    apply sub_eq_zero.mp
    calc
      _ = (deningerL1OriginalGreenCell hf L m - deningerL1OriginalGreenCell hf L (m+1)) -
          (u m - u (m+1)) := by abel
      _ = 0 := by rw [h, sub_self]
  refine ⟨d 0, fun m => ?_⟩
  have hm : d m = d 0 := by
    simpa using hd.int_mul m 0
  dsimp [d] at hm
  simpa only [add_comm] using (sub_eq_iff_eq_add).mp hm

/-- Both endpoint limits follow from the source equation; neither is an added premise. -/
theorem deningerL1OriginalGreenCell_any_primitive_ends
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L)
    (u : ℤ → DeningerOriginalCellL1 L)
    (hu : ∀ m, u m - u (m+1) = deningerOriginalSourceCell hf L m) :
    ∃ c : DeningerOriginalCellL1 L,
      Tendsto (fun n : ℕ => u n) atTop (𝓝 c) ∧
      Tendsto (fun n : ℕ => u (-n)) atTop (𝓝 (deningerL1OriginalBoundaryJump hf L + c)) := by
  obtain ⟨c, hc⟩ := deningerL1OriginalGreenCell_primitive_classification hf hL u hu
  refine ⟨c, ?_, ?_⟩
  · simpa only [hc, zero_add] using (deningerL1OriginalGreenCell_positive_end hf L).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
  · simpa only [hc] using (deningerL1OriginalGreenCell_negative_end hf hL).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))

/-- The complete jump is forced by the source for every original primitive. -/
theorem deningerL1OriginalGreenCell_any_primitive_jump
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L)
    (u : ℤ → DeningerOriginalCellL1 L)
    (hu : ∀ m, u m - u (m+1) = deningerOriginalSourceCell hf L m) :
    Tendsto (fun n : ℕ => u (-n) - u n) atTop
      (𝓝 (deningerL1OriginalBoundaryJump hf L)) := by
  obtain ⟨c, hc⟩ := deningerL1OriginalGreenCell_primitive_classification hf hL u hu
  apply (deningerL1OriginalGreenCell_complete_jump hf hL).congr
  intro n
  rw [hc, hc]
  abel

end RHTower
