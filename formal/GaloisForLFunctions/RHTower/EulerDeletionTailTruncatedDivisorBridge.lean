import GaloisForLFunctions.RHTower.EulerDeletionNestedProjectionCovariance
import GaloisForLFunctions.RHTower.EulerDeletionRefinementBlockTail
import GaloisForLFunctions.RHTower.EulerDeletionSelectedRefinementBlockTail
import GaloisForLFunctions.RHTower.EulerDeletionRefinementBlockEnergy
import GaloisForLFunctions.RHTower.TruncatedMoebiusResidual

/-!
# Physical truncated-divisor form of an Euler-deletion tail

The literal paired Möbius source at each physical cell is exactly its harmonic chord minus the
cumulative truncated Möbius divisor sum.  Consequently a chronological clock increment is one
signed physical interval of that same divisor field.  This is an equality only: no interval
estimate, sign removal, period average, or replacement carrier is used here.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

private theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1)) = ∑ d ∈ Icc 1 N, f d := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- Exact physical all-cell form of the literal paired source. -/
theorem pairedMoebiusSource_eq_truncated_divisor_accumulation (N j : ℕ) :
    pairedMoebiusSource N j =
      ((j + 1 : ℕ) : ℝ) *
        (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
      ∑ k ∈ Icc 1 (j + 1), truncMoebiusDivisorSum N k := by
  have hH :
      (∑ i ∈ range N, ((moebius (i + 1) : ℤ) : ℝ) / ((i : ℝ) + 1) =
        ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (sum_range_succ_eq_sum_Icc
        (fun d => ((moebius d : ℤ) : ℝ) / (d : ℝ)) N)
  have hF :
      (∑ i ∈ range N, ((moebius (i + 1) : ℤ) : ℝ) *
        (((j + 1) / (i + 1) : ℕ) : ℝ)) =
        ∑ k ∈ Icc 1 (j + 1), truncMoebiusDivisorSum N k := by
    calc
      _ = ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) *
          (((j + 1) / d : ℕ) : ℝ) :=
        sum_range_succ_eq_sum_Icc
          (fun d => ((moebius d : ℤ) : ℝ) * (((j + 1) / d : ℕ) : ℝ)) N
      _ = _ := sum_moebius_floor_eq_sum_trunc (j + 1) N
  unfold pairedMoebiusSource
  rw [hH, hF]

/-- Every literal paired-source increment is its harmonic increment minus one signed physical
window of truncated Möbius divisor sums. -/
theorem pairedMoebiusSource_increment_eq_truncated_divisor_window (N j q : ℕ) :
    pairedMoebiusSource N (j + q) - pairedMoebiusSource N j =
      (q : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
        ∑ k ∈ Ioc (j + 1) (j + q + 1), truncMoebiusDivisorSum N k := by
  have hsplit : Icc 1 (j + q + 1) = Icc 1 (j + 1) ∪ Ioc (j + 1) (j + q + 1) := by
    ext k
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisjoint : Disjoint (Icc 1 (j + 1)) (Ioc (j + 1) (j + q + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk hwindow
    simp only [mem_Icc] at hk
    simp only [mem_Ioc] at hwindow
    omega
  rw [pairedMoebiusSource_eq_truncated_divisor_accumulation,
    pairedMoebiusSource_eq_truncated_divisor_accumulation, hsplit,
    Finset.sum_union hdisjoint]
  push_cast
  ring

/-- The strict-future Euler-deletion clock increment is exactly the physical truncated-divisor
window associated with that history clock. -/
theorem pairedMoebiusSource_clock_increment_eq_truncated_divisor_window (N L j : ℕ) :
    pairedMoebiusSource N (j + clock L) - pairedMoebiusSource N j =
      (clock L : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
        ∑ k ∈ Ioc (j + 1) (j + clock L + 1), truncMoebiusDivisorSum N k :=
  pairedMoebiusSource_increment_eq_truncated_divisor_window N j (clock L)

/-- The entire strict-future multi-modulus Euler-deletion tail is the corresponding signed
physical truncated-divisor window.  Every modulus, residue, and Möbius sign remains in this
identity. -/
theorem unprocessed_tail_eq_truncated_divisor_window (N L j : ℕ) :
    (∑ i ∈ range N, if L ≤ i then
      ((moebius (i + 1) : ℤ) : ℝ) *
        (residue (i + 1) (j + clock L) - residue (i + 1) j) else 0) =
      (clock L : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
        ∑ k ∈ Ioc (j + 1) (j + clock L + 1), truncMoebiusDivisorSum N k := by
  rw [← pairedMoebiusSource_clock_increment_eq_unprocessed_tail]
  exact pairedMoebiusSource_clock_increment_eq_truncated_divisor_window N L j

/-- Exact finite β-kernel form of the literal joint-clock source: every weighted strict-future
residue tail is its corresponding signed truncated-divisor window.  This keeps the complete
joint sum intact before the fibre-energy square. -/
theorem pairedMoebiusSource_finite_joint_kernel_eq_truncated_divisor_windows
    (N L r K : ℕ) (y : ℝ) (hK : K * clock L = clock N) :
    (1 - y) * (∑ s ∈ range K,
      y ^ s * pairedMoebiusSource N (r + s * clock L)) =
      (1 - y ^ K) * pairedMoebiusSource N r +
        y * ∑ s ∈ range K, y ^ s *
          ((clock L : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
            ∑ k ∈ Ioc (r + s * clock L + 1) (r + (s + 1) * clock L + 1),
              truncMoebiusDivisorSum N k) := by
  rw [pairedMoebiusSource_finite_joint_kernel_eq_unprocessed_tail N L r K y hK]
  apply congrArg (fun z =>
    (1 - y ^ K) * pairedMoebiusSource N r + y * z)
  apply Finset.sum_congr rfl
  intro s hs
  apply congrArg (fun z => y ^ s * z)
  have harg : r + s * clock L + clock L = r + (s + 1) * clock L := by
    rw [Nat.succ_mul]
    ac_rfl
  rw [← harg]
  rw [unprocessed_tail_eq_truncated_divisor_window]

/-- The actual scaled parent refinement β-kernel is the same literal kernel with every
strict-future tail expressed as its signed physical truncated-divisor window.  The physical
geometric mass, source endpoint, and all joint divisor levels remain unchanged. -/
theorem scaled_canonicalRefinementAggregateKernel_eq_truncated_divisor_windows
    (N l r : ℕ) (hlN : l < N) (x : ℝ) :
    (∑ a ∈ range (clock l), x ^ a) * canonicalRefinementAggregateKernel N l r x =
      x ^ r *
        (((1 - x ^ clock N) * pairedMoebiusSource N r +
          x ^ clock l * ∑ s ∈ range (canonicalClockRatio N l), x ^ (s * clock l) *
            ((clock l : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
              ∑ k ∈ Ioc (r + s * clock l + 1) (r + (s + 1) * clock l + 1),
                truncMoebiusDivisorSum N k)) *
          (1 - x ^ clock N)⁻¹) := by
  rw [scaled_canonicalRefinementAggregateKernel_eq_unprocessed_tail N l r hlN x]
  apply congrArg (fun z =>
    x ^ r * (((1 - x ^ clock N) * pairedMoebiusSource N r + x ^ clock l * z) *
      (1 - x ^ clock N)⁻¹))
  apply Finset.sum_congr rfl
  intro s hs
  apply congrArg (fun z => x ^ (s * clock l) * z)
  have harg : r + s * clock l + clock l = r + (s + 1) * clock l := by
    rw [Nat.succ_mul]
    ac_rfl
  rw [← harg]
  rw [unprocessed_tail_eq_truncated_divisor_window]

private theorem geom_clock_sum_ne_zero {x : ℝ} (hx : 0 ≤ x) (L : ℕ) :
    (∑ a ∈ range (clock L), x ^ a) ≠ 0 :=
  (geom_sum_pos hx (clock_pos L).ne').ne'

/-- Every adjacent chronological layer has exactly zero physical integral on each lower fibre.
This is the selected-child minus complete-parent cancellation before squaring: both projections
preserve the literal integral on that lower fibre. -/
theorem historyLayer_integral_lower_fibre_eq_zero
    (l r : ℕ) (v : Lp ℝ 2 cellMeasure) :
    ∫ j in historyFibre l r, (historyLayer l v) j ∂cellMeasure = 0 := by
  have hlowerMeas : MeasurableSet[residueSigma (clock l)] (historyFibre l r) := by
    change MeasurableSet[MeasurableSpace.comap (fun j : ℕ => j % clock l) ⊤] _
    exact MeasurableSpace.measurableSet_comap.mpr
      ⟨{r}, (Set.to_countable _).measurableSet, rfl⟩
  have hupperMeas : MeasurableSet[residueSigma (clock (l + 1))] (historyFibre l r) :=
    (residueSigma_mono (clock_dvd (by omega))) _ hlowerMeas
  have hLower := integral_condExpL2_eq (E' := ℝ) (𝕜 := ℝ)
    (m := residueSigma (clock l)) (m0 := (inferInstance : MeasurableSpace ℕ))
    (μ := cellMeasure)
    (show residueSigma (clock l) ≤ (inferInstance : MeasurableSpace ℕ) from le_top)
    v hlowerMeas (measure_ne_top _ _)
  have hUpper := integral_condExpL2_eq (E' := ℝ) (𝕜 := ℝ)
    (m := residueSigma (clock (l + 1))) (m0 := (inferInstance : MeasurableSpace ℕ))
    (μ := cellMeasure)
    (show residueSigma (clock (l + 1)) ≤ (inferInstance : MeasurableSpace ℕ) from le_top)
    v hupperMeas (measure_ne_top _ _)
  have hLower' : ∫ j in historyFibre l r,
      ((historySpace l).starProjection v) j ∂cellMeasure =
      ∫ j in historyFibre l r, v j ∂cellMeasure := by
    simpa only [historySpace, condExpL2, Submodule.starProjection_apply] using hLower
  have hUpper' : ∫ j in historyFibre l r,
      ((historySpace (l + 1)).starProjection v) j ∂cellMeasure =
      ∫ j in historyFibre l r, v j ∂cellMeasure := by
    simpa only [historySpace, condExpL2, Submodule.starProjection_apply] using hUpper
  let upper : Lp ℝ 2 cellMeasure := (historySpace (l + 1)).starProjection v
  let lower : Lp ℝ 2 cellMeasure := (historySpace l).starProjection v
  have hUpperInt : Integrable (upper : ℕ → ℝ) cellMeasure :=
    (Lp.memLp upper).integrable one_le_two
  have hLowerInt : Integrable (lower : ℕ → ℝ) cellMeasure :=
    (Lp.memLp lower).integrable one_le_two
  change ∫ j in historyFibre l r, (upper - lower) j ∂cellMeasure = 0
  rw [show (∫ j in historyFibre l r, (upper - lower) j ∂cellMeasure) =
      ∫ j in historyFibre l r, (upper j - lower j) ∂cellMeasure by
        exact setIntegral_congr_ae (Set.to_countable _).measurableSet
          ((Lp.coeFn_sub upper lower).mono fun _ h _ => h)]
  rw [integral_sub hUpperInt.integrableOn hLowerInt.integrableOn]
  change (∫ j in historyFibre l r,
      ((historySpace (l + 1)).starProjection v) j ∂cellMeasure) -
      ∫ j in historyFibre l r,
      ((historySpace l).starProjection v) j ∂cellMeasure = 0
  rw [hUpper', hLower', sub_self]

/-- Pointwise physical β form of the complete parent refinement aggregate.  The denominator is
only its literal positive geometric mass; the numerator remains the complete signed window
field. -/
theorem canonicalRefinementAggregateKernel_eq_truncated_divisor_windows_div_geom
    (N l r : ℕ) (hlN : l < N) (x : ℝ) (hx : 0 ≤ x) :
    canonicalRefinementAggregateKernel N l r x =
      (x ^ r *
        (((1 - x ^ clock N) * pairedMoebiusSource N r +
          x ^ clock l * ∑ s ∈ range (canonicalClockRatio N l), x ^ (s * clock l) *
            ((clock l : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
              ∑ k ∈ Ioc (r + s * clock l + 1) (r + (s + 1) * clock l + 1),
                truncMoebiusDivisorSum N k)) *
          (1 - x ^ clock N)⁻¹)) /
        (∑ a ∈ range (clock l), x ^ a) := by
  apply (eq_div_iff (geom_clock_sum_ne_zero hx l)).mpr
  rw [mul_comm]
  exact scaled_canonicalRefinementAggregateKernel_eq_truncated_divisor_windows N l r hlN x

/-- The selected child refinement β-kernel has the same signed physical window form as its
complete parent aggregate.  Its start is the actual selected child residue; no child block is
averaged or replaced. -/
theorem scaled_canonicalRefinementBlockKernel_eq_truncated_divisor_windows
    (N l u b : ℕ) (hlN : l < N) (x : ℝ) :
    (∑ a ∈ range (clock (l + 1)), x ^ a) * canonicalRefinementBlockKernel N l u b x =
      x ^ (u + b * clock l) *
        (((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) *
            ∑ s ∈ range (canonicalClockRatio N (l + 1)), x ^ (s * clock (l + 1)) *
              ((clock (l + 1) : ℝ) *
                  (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
                ∑ k ∈ Ioc (u + b * clock l + s * clock (l + 1) + 1)
                  (u + b * clock l + (s + 1) * clock (l + 1) + 1),
                  truncMoebiusDivisorSum N k)) *
          (1 - x ^ clock N)⁻¹) := by
  rw [scaled_canonicalRefinementBlockKernel_eq_unprocessed_tail N l u b hlN x]
  apply congrArg (fun z =>
    x ^ (u + b * clock l) *
      (((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
        x ^ clock (l + 1) * z) * (1 - x ^ clock N)⁻¹))
  apply Finset.sum_congr rfl
  intro s hs
  apply congrArg (fun z => x ^ (s * clock (l + 1)) * z)
  have harg :
      u + b * clock l + s * clock (l + 1) + clock (l + 1) =
        u + b * clock l + (s + 1) * clock (l + 1) := by
    rw [Nat.succ_mul]
    ac_rfl
  rw [← harg]
  rw [unprocessed_tail_eq_truncated_divisor_window]

/-- Pointwise physical β form of one literal selected child block.  It uses the same complete
signed window field, with the child's unaltered starting residue. -/
theorem canonicalRefinementBlockKernel_eq_truncated_divisor_windows_div_geom
    (N l u b : ℕ) (hlN : l < N) (x : ℝ) (hx : 0 ≤ x) :
    canonicalRefinementBlockKernel N l u b x =
      (x ^ (u + b * clock l) *
        (((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) *
            ∑ s ∈ range (canonicalClockRatio N (l + 1)), x ^ (s * clock (l + 1)) *
              ((clock (l + 1) : ℝ) *
                  (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
                ∑ k ∈ Ioc (u + b * clock l + s * clock (l + 1) + 1)
                  (u + b * clock l + (s + 1) * clock (l + 1) + 1),
                  truncMoebiusDivisorSum N k)) *
          (1 - x ^ clock N)⁻¹)) /
        (∑ a ∈ range (clock (l + 1)), x ^ a) := by
  apply (eq_div_iff (geom_clock_sum_ne_zero hx (l + 1))).mpr
  rw [mul_comm]
  exact scaled_canonicalRefinementBlockKernel_eq_truncated_divisor_windows N l u b hlN x

/-- Literal signed truncated-divisor window kernel of the complete parent refinement block. -/
def truncatedDivisorAggregateKernel (N l r : ℕ) (x : ℝ) : ℝ :=
  (x ^ r *
    (((1 - x ^ clock N) * pairedMoebiusSource N r +
      x ^ clock l * ∑ s ∈ range (canonicalClockRatio N l), x ^ (s * clock l) *
        ((clock l : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
          ∑ k ∈ Ioc (r + s * clock l + 1) (r + (s + 1) * clock l + 1),
            truncMoebiusDivisorSum N k)) *
      (1 - x ^ clock N)⁻¹)) /
    (∑ a ∈ range (clock l), x ^ a)

/-- Literal signed truncated-divisor window kernel of one selected child refinement block. -/
def truncatedDivisorBlockKernel (N l u b : ℕ) (x : ℝ) : ℝ :=
  (x ^ (u + b * clock l) *
    (((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
      x ^ clock (l + 1) *
        ∑ s ∈ range (canonicalClockRatio N (l + 1)), x ^ (s * clock (l + 1)) *
          ((clock (l + 1) : ℝ) *
              (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
            ∑ k ∈ Ioc (u + b * clock l + s * clock (l + 1) + 1)
              (u + b * clock l + (s + 1) * clock (l + 1) + 1),
              truncMoebiusDivisorSum N k)) *
      (1 - x ^ clock N)⁻¹)) /
    (∑ a ∈ range (clock (l + 1)), x ^ a)

/-- The complete parent kernel equals its literal signed truncated-divisor window form at each
physical β coordinate. -/
theorem canonicalRefinementAggregateKernel_eq_truncatedDivisorAggregateKernel
    (N l r : ℕ) (hlN : l < N) (x : ℝ) (hx : 0 ≤ x) :
    canonicalRefinementAggregateKernel N l r x =
      truncatedDivisorAggregateKernel N l r x := by
  simpa only [truncatedDivisorAggregateKernel] using
    canonicalRefinementAggregateKernel_eq_truncated_divisor_windows_div_geom N l r hlN x hx

/-- The selected child kernel equals its literal signed truncated-divisor window form at each
physical β coordinate. -/
theorem canonicalRefinementBlockKernel_eq_truncatedDivisorBlockKernel
    (N l u b : ℕ) (hlN : l < N) (x : ℝ) (hx : 0 ≤ x) :
    canonicalRefinementBlockKernel N l u b x =
      truncatedDivisorBlockKernel N l u b x := by
  simpa only [truncatedDivisorBlockKernel] using
    canonicalRefinementBlockKernel_eq_truncated_divisor_windows_div_geom N l u b hlN x hx

/-- The literal selected-child minus complete-parent minus innovation coordinate in the signed
truncated-divisor window field.  The upper residue remains the actual physical cell residue. -/
def truncatedDivisorWindowContrast (N l j : ℕ) : ℝ :=
  let r := j % clock (l + 1)
  (∫ x in (0 : ℝ)..1,
    truncatedDivisorBlockKernel N l (r % clock l) (r / clock l) x) /
      cellMeasure.real
        (historyFibre (l + 1) ((r % clock l) + (r / clock l) * clock l)) -
    (∫ x in (0 : ℝ)..1,
      truncatedDivisorAggregateKernel N l (r % clock l) x) /
        cellMeasure.real (historyFibre l (r % clock l)) -
    signedInnovation l j

/-- Exact physical-cell form of the EDQ layer in its selected-child/parent window contrast.
It retains the joint signed field before any cross-layer argument. -/
theorem historyLayer_predictableDrift_apply_eq_truncatedDivisorWindowContrast
    (l N j : ℕ) (hlN : l < N) :
    (historyLayer l (predictableDrift N)) j = truncatedDivisorWindowContrast N l j := by
  let r := j % clock (l + 1)
  have hjmod : j % clock l = r % clock l := by
    dsimp only [r]
    exact (Nat.mod_mod_of_dvd j (clock_dvd (by omega))).symm
  have hblock :
      (∫ x in (0 : ℝ)..1,
        canonicalRefinementBlockKernel N l (r % clock l) (r / clock l) x) =
        ∫ x in (0 : ℝ)..1,
          truncatedDivisorBlockKernel N l (r % clock l) (r / clock l) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa using hx
    exact canonicalRefinementBlockKernel_eq_truncatedDivisorBlockKernel N l
      (r % clock l) (r / clock l) hlN x hx'.1
  have haggregate :
      (∫ x in (0 : ℝ)..1, canonicalRefinementAggregateKernel N l (r % clock l) x) =
        ∫ x in (0 : ℝ)..1, truncatedDivisorAggregateKernel N l (r % clock l) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa using hx
    exact canonicalRefinementAggregateKernel_eq_truncatedDivisorAggregateKernel N l
      (r % clock l) hlN x hx'.1
  rw [historyLayer_predictableDrift_apply_eq_canonicalBetaResolvent_sub_innovation l N j hlN,
    hjmod,
    canonicalBetaResolvent_succ_sub_lower_eq_refinementBlockKernel_difference_mod_div l N r hlN,
    hblock, haggregate]
  rfl

/-- Exact lower-fibre cancellation of the literal truncated-divisor selected-child/parent
contrast.  This is a joint signed identity, not an estimate of any summand or a period average. -/
theorem truncatedDivisorWindowContrast_integral_lower_fibre_eq_zero
    (l N q : ℕ) (hlN : l < N) :
    ∫ j in historyFibre l q, truncatedDivisorWindowContrast N l j ∂cellMeasure = 0 := by
  calc
    ∫ j in historyFibre l q, truncatedDivisorWindowContrast N l j ∂cellMeasure =
        ∫ j in historyFibre l q, (historyLayer l (predictableDrift N)) j ∂cellMeasure := by
      apply setIntegral_congr_fun (Set.to_countable _).measurableSet
      intro j _
      exact (historyLayer_predictableDrift_apply_eq_truncatedDivisorWindowContrast l N j hlN).symm
    _ = 0 := historyLayer_integral_lower_fibre_eq_zero l q (predictableDrift N)

/-- Exact prime-power EDQ layer energy in the signed truncated-divisor-window coordinates.  Every
term in the displayed square is still the selected physical block, complete parent aggregate,
and local innovation at its original fibre mass. -/
theorem historyLayer_predictableDrift_norm_sq_eq_truncatedDivisorWindow_energy
    (l N : ℕ) (hlN : l < N) :
    ‖historyLayer l (predictableDrift N)‖ ^ 2 =
      ∑ r ∈ range (clock (l + 1)),
        cellMeasure.real (historyFibre (l + 1) r) *
          ((∫ x in (0 : ℝ)..1,
            truncatedDivisorBlockKernel N l (r % clock l) (r / clock l) x) /
              cellMeasure.real
                (historyFibre (l + 1) ((r % clock l) + (r / clock l) * clock l)) -
            (∫ x in (0 : ℝ)..1,
              truncatedDivisorAggregateKernel N l (r % clock l) x) /
                cellMeasure.real (historyFibre l (r % clock l)) -
            signedInnovation l r) ^ 2 := by
  rw [historyLayer_predictableDrift_norm_sq_eq_refinementBlockKernel_energy l N hlN]
  apply Finset.sum_congr rfl
  intro r hr
  have hblock :
      (∫ x in (0 : ℝ)..1,
        canonicalRefinementBlockKernel N l (r % clock l) (r / clock l) x) =
        ∫ x in (0 : ℝ)..1,
          truncatedDivisorBlockKernel N l (r % clock l) (r / clock l) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa using hx
    exact canonicalRefinementBlockKernel_eq_truncatedDivisorBlockKernel N l
      (r % clock l) (r / clock l) hlN x hx'.1
  have haggregate :
      (∫ x in (0 : ℝ)..1, canonicalRefinementAggregateKernel N l (r % clock l) x) =
        ∫ x in (0 : ℝ)..1, truncatedDivisorAggregateKernel N l (r % clock l) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa using hx
    exact canonicalRefinementAggregateKernel_eq_truncatedDivisorAggregateKernel N l
      (r % clock l) hlN x hx'.1
  rw [hblock, haggregate]

/-- Full EDQ predictable-drift energy in the literal signed truncated-divisor-window coordinates.
The remaining theorem is precisely a cofinal polylogarithmic bound for this displayed complete
prime-power sum. -/
theorem predictableDrift_norm_sq_eq_primePower_truncatedDivisorWindow_energy (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
        ∑ l ∈ (range N).filter (fun l => IsPrimePow (l + 1)),
          ∑ r ∈ range (clock (l + 1)),
            cellMeasure.real (historyFibre (l + 1) r) *
              ((∫ x in (0 : ℝ)..1,
                truncatedDivisorBlockKernel N l (r % clock l) (r / clock l) x) /
                  cellMeasure.real
                    (historyFibre (l + 1) ((r % clock l) + (r / clock l) * clock l)) -
                (∫ x in (0 : ℝ)..1,
                  truncatedDivisorAggregateKernel N l (r % clock l) x) /
                    cellMeasure.real (historyFibre l (r % clock l)) -
                signedInnovation l r) ^ 2 := by
  rw [predictableDrift_norm_sq_eq_historyLayer_sum,
    predictableDrift_historyLayer_energy_eq_primePower_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  exact historyLayer_predictableDrift_norm_sq_eq_truncatedDivisorWindow_energy l N
    (Finset.mem_range.mp (Finset.mem_of_mem_filter l hl))

end RHTower.DeletionResidueMartingale
