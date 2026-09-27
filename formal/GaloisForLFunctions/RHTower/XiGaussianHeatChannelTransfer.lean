import GaloisForLFunctions.RHTower.XiGaussianNativeHeatDissipation
import GaloisForLFunctions.RHTower.XiGaussianRealChannelEnergy
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLadder

/-!
# A degree-uniform budget for heat-generated phase transfer

The real and imaginary amplitude channels, each corrected by `K / 81`,
decrease under heating. Their combined positive gain on any increasing
finite time partition is at most one eighty-first of the native energy
dissipated over that partition. The complete prime--Gamma source and every
Hankel order obey the corresponding signed variation bound.

These are unconditional transport bounds. They do not supply an initial
real-channel fraction or prove positivity at a fixed heat time.
-/

open Complex Filter Topology
open scoped BigOperators Real
noncomputable section
namespace RHTower

/-- The imaginary channel can only gain energy by spending a small fraction
of native heat dissipation, with no restriction on polynomial degree. -/
theorem xiGaussian_imaginaryChannel_corrected_antitone (P : Polynomial ℝ) :
    Antitone (fun t : {t : ℝ // 0 < t} =>
      81 * (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q) +
        xiGaussianNativeEnergy P t) := by
  intro s t hst
  have h := xiGaussianNative_corrected_trace_antitone P
    ⟨-1, by constructor <;> norm_num⟩ hst
  dsimp only at h ⊢
  rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace,
    xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace]
  linarith only [h]

/-- The same dissipation budget controls gains of the complete real channel. -/
theorem xiGaussian_realChannel_corrected_antitone (P : Polynomial ℝ) :
    Antitone (fun t : {t : ℝ // 0 < t} =>
      81 * xiGaussianRealChannelEnergy P t + xiGaussianNativeEnergy P t) := by
  intro s t hst
  have h := xiGaussianNative_corrected_trace_antitone P
    ⟨1, by constructor <;> norm_num⟩ hst
  dsimp only at h ⊢
  rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace,
    xiGaussianRealChannelEnergy_eq_half_energy_add_trace]
  change 81 * ((xiGaussianNativeEnergy P t + xiPolynomialGaussianHeatTraceReal P t) / 2) +
    xiGaussianNativeEnergy P t ≤
    81 * ((xiGaussianNativeEnergy P s + xiPolynomialGaussianHeatTraceReal P s) / 2) +
      xiGaussianNativeEnergy P s
  linarith only [h]

/-- Total positive gain of the two complete amplitude channels. -/
def xiGaussianHeatChannelTransfer (P : Polynomial ℝ)
    (s t : {t : ℝ // 0 < t}) : ℝ :=
  max 0 ((∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q) -
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P s q)) +
  max 0 (xiGaussianRealChannelEnergy P t - xiGaussianRealChannelEnergy P s)

/-- At most one channel grows during an interval of heating. Their combined
positive gain costs at most `1 / 81` of the full native energy lost. -/
theorem xiGaussianHeatChannelTransfer_le_native_dissipation
    (P : Polynomial ℝ) (s : {s : ℝ // 0 < s})
    (t : Set.Ici (s : ℝ)) :
    xiGaussianHeatChannelTransfer P s (xiGaussianHeatAfter s t) ≤
      (xiGaussianNativeEnergy P s -
        xiGaussianNativeEnergy P (xiGaussianHeatAfter s t)) / 81 := by
  let u := xiGaussianHeatAfter s t
  have hu : s ≤ u := t.property
  have hI := xiGaussian_imaginaryChannel_corrected_antitone P hu
  have hJ := xiGaussian_realChannel_corrected_antitone P hu
  have hK := xiGaussianNativeEnergy_antitone P hu
  let Is := ∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P s q
  let It := ∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P u q
  let Js := xiGaussianRealChannelEnergy P s
  let Jt := xiGaussianRealChannelEnergy P u
  have hsplit (v : {t : ℝ // 0 < t}) :
      (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P v q) +
        xiGaussianRealChannelEnergy P v = xiGaussianNativeEnergy P v := by
    rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace,
      xiGaussianRealChannelEnergy_eq_half_energy_add_trace]
    change (xiGaussianNativeEnergy P v - xiPolynomialGaussianHeatTraceReal P v) / 2 +
      (xiGaussianNativeEnergy P v + xiPolynomialGaussianHeatTraceReal P v) / 2 = _
    ring
  have hbalance : (It - Is) + (Jt - Js) ≤ 0 := by
    have hs := hsplit s
    have ht := hsplit u
    change Is + Js = _ at hs
    change It + Jt = _ at ht
    linarith only [hs, ht, hK]
  have hIgain : It - Is ≤ (xiGaussianNativeEnergy P s - xiGaussianNativeEnergy P u) / 81 := by
    change 81 * It + xiGaussianNativeEnergy P u ≤
      81 * Is + xiGaussianNativeEnergy P s at hI
    linarith only [hI]
  have hJgain : Jt - Js ≤ (xiGaussianNativeEnergy P s - xiGaussianNativeEnergy P u) / 81 := by
    change 81 * Jt + xiGaussianNativeEnergy P u ≤
      81 * Js + xiGaussianNativeEnergy P s at hJ
    linarith only [hJ]
  have hbudget : 0 ≤ (xiGaussianNativeEnergy P s - xiGaussianNativeEnergy P u) / 81 :=
    div_nonneg (sub_nonneg.mpr hK) (by positivity)
  change max 0 (It - Is) + max 0 (Jt - Js) ≤ _
  by_cases hI0 : It - Is ≤ 0
  · rw [max_eq_left hI0, zero_add]
    exact max_le hbudget hJgain
  · have hIp : 0 ≤ It - Is := (lt_of_not_ge hI0).le
    have hJ0 : Jt - Js ≤ 0 := by linarith only [hbalance, hIp]
    rw [max_eq_right hIp, max_eq_left hJ0, add_zero]
    exact hIgain

/-- A single native-energy budget controls all positive channel transfer
along every finite increasing heat partition, independently of its length. -/
theorem sum_xiGaussianHeatChannelTransfer_le_native_dissipation
    (P : Polynomial ℝ)
    (τ : {τ : ℕ → {t : ℝ // 0 < t} // Monotone τ}) (n : ℕ) :
    (∑ i ∈ Finset.range n, xiGaussianHeatChannelTransfer P (τ.1 i) (τ.1 (i + 1))) ≤
      (xiGaussianNativeEnergy P (τ.1 0) - xiGaussianNativeEnergy P (τ.1 n)) / 81 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn := xiGaussianHeatChannelTransfer_le_native_dissipation P (τ.1 n)
      ⟨τ.1 (n + 1), τ.property (Nat.le_succ n)⟩
    change xiGaussianHeatChannelTransfer P (τ.1 n) (τ.1 (n + 1)) ≤
      (xiGaussianNativeEnergy P (τ.1 n) - xiGaussianNativeEnergy P (τ.1 (n + 1))) / 81 at hn
    linarith only [ih, hn]

/-- The full arithmetic source obeys the same variation bound; its polar,
Gamma and complete prime terms have already been combined before estimating. -/
theorem abs_xiGaussianCompletedSource_sub_le_native_dissipation
    (P : Polynomial ℝ) (s : {s : ℝ // 0 < s})
    (t : Set.Ici (s : ℝ)) :
    |xiGaussianCompletedSourceResidual P (xiGaussianHeatAfter s t) -
      xiGaussianCompletedSourceResidual P s| ≤
      π * (83 / 81 : ℝ) * (xiGaussianNativeEnergy P s -
        xiGaussianNativeEnergy P (xiGaussianHeatAfter s t)) := by
  rw [xiGaussianCompletedSourceResidual_eq_trace, xiGaussianCompletedSourceResidual_eq_trace,
    ← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
  exact (mul_le_mul_of_nonneg_left
    (abs_xiGaussianHeatTraceReal_sub_le_native_dissipation P s t) Real.pi_pos.le).trans_eq
      (mul_assoc _ _ _).symm

/-- Every coefficient cross term of every actual Xi Hankel order satisfies
one common heat-dissipation estimate. The time interval never depends on order. -/
theorem abs_xiHeatHankelForm_sub_le_native_dissipation
    (N : ℕ) (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
    (t : Set.Ici (s : ℝ)) :
    let P := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
    |xiHeatHankelForm N a t - xiHeatHankelForm N a s| ≤
      (83 / 81 : ℝ) * (xiGaussianNativeEnergy P s -
        xiGaussianNativeEnergy P (xiGaussianHeatAfter s t)) := by
  dsimp only
  have ht : 0 < (t : ℝ) := lt_of_lt_of_le s.property t.property
  rw [← xiPolynomialGaussianHeatTraceReal_rangeSum ht,
    ← xiPolynomialGaussianHeatTraceReal_rangeSum s.property]
  exact abs_xiGaussianHeatTraceReal_sub_le_native_dissipation _ s t

end RHTower
