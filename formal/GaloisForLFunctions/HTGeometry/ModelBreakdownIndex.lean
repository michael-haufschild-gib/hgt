/-
Where the independent-signs model crosses the main term, and what the Lindelöf hypothesis costs.

The model predicts the `2k`-th moment error `E_k(T) ≍ T^{1/2 + k(s-1/2)/2}` from the typical size
`M^{s}` of the correlation error, at the balanced length `M = T^{k/2}`.  The main term of the moment
is `≍ T` up to logarithms.  Two consequences follow from comparing them.

**The critical index is `4`.**  With Ivić's size `s = 1 - 1/k` the prediction is `T^{k/4}`, which
equals the main term exactly at `k = 4` and exceeds it for `k > 4`.  This is the arithmetic behind
three criticalities the campaign met separately: the pointwise branch of the transfer saturates at
`k ≤ 4`; Ivić's size meets the moment envelope with equality at `k = 4`; and the size cap forced by
the Lindelöf hypothesis is met with equality at `k = 4`.

**What the Lindelöf hypothesis costs.**  `m(k) = 1` for every `k` forces
`1/2 + k(s-1/2)/2 ≤ 1`, i.e. `s ≤ 1/2 + 1/k`.  So the Lindelöf hypothesis demands that the
correlation size exponent tend to the square-root value `1/2` — and Ivić's law satisfies the demand
exactly for `k ≤ 4`, violating it from `k = 5` on.  The curve `1/2 + 1/k` is the same curve as the
chord-beating threshold of the averaged input.
-/
import GaloisForLFunctions.HTGeometry.CorrelationSizeUniqueness

namespace HTGeometry

/-- The moment exponent predicted by the model with Ivić's size: `max(1, k/4)`. -/
noncomputable def modelMomentExponent (k : ℝ) : ℝ := max 1 (k/4)

/-- **The model's error crosses the main term exactly at `k = 4`.** -/
theorem modelMomentExponent_gt_one_iff {k : ℝ} : 1 < modelMomentExponent k ↔ 4 < k := by
  unfold modelMomentExponent
  constructor
  · intro h
    rcases max_cases 1 (k/4) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at h; linarith
    · rw [he] at h; linarith
  · intro h
    have : (1 : ℝ) < k/4 := by linarith
    exact lt_of_lt_of_le this (le_max_right _ _)

@[simp] theorem modelMomentExponent_four : modelMomentExponent 4 = 1 := by
  unfold modelMomentExponent; norm_num

/-- **The model, extended to every index, contradicts the Lindelöf hypothesis.**  Lindelöf requires
`m(k) = 1` for all `k`; the model gives `m(k) = k/4 > 1` for `k > 4`. -/
theorem model_contradicts_lindelof (h : ∀ k : ℝ, 0 < k → modelMomentExponent k = 1) : False := by
  have h5 := h 5 (by norm_num)
  have : (1 : ℝ) < modelMomentExponent 5 := modelMomentExponent_gt_one_iff.mpr (by norm_num)
  rw [h5] at this
  exact lt_irrefl 1 this

/-- The size-exponent cap that the Lindelöf hypothesis imposes through the model. -/
noncomputable def lindelofSizeCap (k : ℝ) : ℝ := 1/2 + 1/k

/-- **Lindelöf forces the size cap.**  `modelPrediction k s ≤ 1` is exactly `s ≤ 1/2 + 1/k`. -/
theorem lindelof_forces_size_cap {k s : ℝ} (hk : 0 < k) :
    modelPrediction k s ≤ 1 ↔ s ≤ lindelofSizeCap k := by
  unfold modelPrediction lindelofSizeCap
  constructor
  · intro h
    have hk' : k ≠ 0 := ne_of_gt hk
    rw [← sub_le_iff_le_add']
    rw [le_div_iff₀ hk]
    nlinarith [h]
  · intro h
    have h' : s - 1/2 ≤ 1/k := by linarith
    have : k * (s - 1/2) ≤ k * (1/k) := by
      exact mul_le_mul_of_nonneg_left h' hk.le
    rw [mul_one_div, div_self (ne_of_gt hk)] at this
    linarith

/-- **Ivić's size meets the Lindelöf cap exactly at `k ≤ 4`.**  Both statements `1 - 1/k ≤ 1/2 + 1/k`
and `k ≤ 4` are the same. -/
theorem ivicSize_le_cap_iff {k : ℝ} (hk : 0 < k) :
    ivicSize k ≤ lindelofSizeCap k ↔ k ≤ 4 := by
  unfold ivicSize lindelofSizeCap
  constructor
  · intro h
    have h2 : (1 : ℝ)/2 ≤ 2 * (1/k) := by linarith
    rw [mul_one_div, le_div_iff₀ hk] at h2
    linarith
  · intro h
    have h2 : (1 : ℝ)/2 ≤ 2 * (1/k) := by
      rw [mul_one_div, le_div_iff₀ hk]; linarith
    linarith

/-- The cap tends to the square-root value: Lindelöf demands the correlation error be of
square-root size in the limit. -/
theorem lindelofSizeCap_tendsto_half :
    Filter.Tendsto lindelofSizeCap Filter.atTop (nhds (1/2)) := by
  unfold lindelofSizeCap
  have := Filter.Tendsto.const_add (1/2 : ℝ) tendsto_inv_atTop_zero
  simpa [one_div] using this

/-- **The critical index, assembled.**  At `k = 4`: the model's error equals the main term; Ivić's
size equals the Lindelöf cap; and the pointwise branch of the transfer saturates.  Three
criticalities the campaign met separately are one. -/
theorem critical_index_four :
    modelMomentExponent 4 = 1 ∧
    ivicSize 4 = lindelofSizeCap 4 ∧
    (transferBound 4 1 (1/2) = 1) := by
  refine ⟨modelMomentExponent_four, ?_, ?_⟩
  · unfold ivicSize lindelofSizeCap; norm_num
  · rw [pointwise_input_eq_one_iff]; norm_num

/-- The Lindelöf hypothesis, expressed on the moment exponents: `m(k) = 1` for every positive `k`.
(`m ≥ 1` always, so this is the same as `m(k) ≤ 1`.) -/
def LindelofOnMoments (m : ℝ → ℝ) : Prop := ∀ k : ℝ, 0 < k → m k = 1

/-- **A power-excess lower bound at any single index disproves Lindelöf.**  This is the campaign's
only disproof branch, and it is not excluded by the resonance ceiling: a moment lower bound is not a
resonance construction. -/
theorem power_excess_disproves_lindelof {m : ℝ → ℝ} {k : ℝ} (hk : 0 < k) (h : 1 < m k) :
    ¬ LindelofOnMoments m := by
  intro hL
  rw [hL k hk] at h
  exact lt_irrefl 1 h

/-- Concretely at the tenth moment: `∫_0^T|ζ(1/2+it)|^{10}dt ≫ T^{5/4}` would disprove Lindelöf. -/
theorem tenth_moment_excess_disproves {m : ℝ → ℝ} (h : 5/4 ≤ m 5) : ¬ LindelofOnMoments m :=
  power_excess_disproves_lindelof (k := 5) (by norm_num) (by linarith)

/-- **The model predicts exactly that excess.**  So the disproof branch is not speculative: it is the
model's own prediction at the first index where the model exceeds the main term. -/
theorem model_predicts_tenth_moment_excess : modelMomentExponent 5 = 5/4 := by
  unfold modelMomentExponent
  rw [max_eq_right (by norm_num)]

/-- **The dichotomy, closed.**  Either the size cap `s ≤ 1/2 + 1/k` holds at every index — and then
the model gives `m(k) = 1` throughout, consistent with Lindelöf — or it fails at some `k > 4`, and
then that index carries a power excess which disproves Lindelöf.  There is no third possibility
inside the model. -/
theorem size_cap_dichotomy {k s : ℝ} (hk : 0 < k) :
    (s ≤ lindelofSizeCap k ∧ modelPrediction k s ≤ 1) ∨
    (lindelofSizeCap k < s ∧ 1 < modelPrediction k s) := by
  rcases le_or_gt s (lindelofSizeCap k) with h | h
  · exact Or.inl ⟨h, (lindelof_forces_size_cap hk).mpr h⟩
  · refine Or.inr ⟨h, ?_⟩
    by_contra hc
    rw [not_lt] at hc
    exact absurd ((lindelof_forces_size_cap hk).mp hc) (not_le.mpr h)

/-- The Riemann hypothesis, in the only form used here: it forces every moment exponent to `1`.
This is Harper's theorem (following Soundararajan), `∫_0^T|ζ(1/2+it)|^{2k}dt ≪ T(log T)^{k²}` under
RH for every fixed `k ≥ 0`. -/
def RHOnMoments (m : ℝ → ℝ) : Prop := ∀ k : ℝ, 0 < k → m k = 1

/-- **The disproof branch implies the falsity of the Riemann hypothesis.**  A power excess at any
index contradicts the conditional upper bound, so the only disproof route the campaign has found is
strictly harder than disproving RH. -/
theorem power_excess_implies_not_rh {m : ℝ → ℝ} {k : ℝ} (hk : 0 < k) (h : 1 < m k) :
    ¬ RHOnMoments m := by
  intro hR
  rw [hR k hk] at h
  exact lt_irrefl 1 h

/-- **The Riemann hypothesis refutes the independent-signs model at `k = 5`.**  Under RH every moment
exponent is `1`, while the model asserts `5/4`.  So the model — exact at both solved indices, and the
source of the pivot `1/8` — cannot be extrapolated past `k = 4`. -/
theorem rh_refutes_model {m : ℝ → ℝ} (hR : RHOnMoments m) :
    m 5 ≠ modelMomentExponent 5 := by
  rw [hR 5 (by norm_num), model_predicts_tenth_moment_excess]
  norm_num

/-- **Under RH the size cap holds at every index.**  Combined with `size_cap_dichotomy`, RH forces
`s ≤ 1/2 + 1/k` throughout — that is, it decides the Conrey–Gonek/Ivić dichotomy in favour of the
square-root size for every `k ≥ 5`, where the two differ. -/
theorem rh_forces_size_cap {m : ℝ → ℝ} {k s : ℝ} (hk : 0 < k) (hR : RHOnMoments m)
    (hmodel : m k = modelPrediction k s) : s ≤ lindelofSizeCap k := by
  rw [← lindelof_forces_size_cap hk, ← hmodel, hR k hk]

/-- The index beyond which RH and the model disagree is exactly `4`: the model is compatible with RH
precisely on `k ≤ 4`. -/
theorem model_rh_compatible_iff {k : ℝ} : modelMomentExponent k = 1 ↔ k ≤ 4 := by
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have := modelMomentExponent_gt_one_iff.mpr hc
    rw [h] at this
    exact lt_irrefl 1 this
  · intro h
    unfold modelMomentExponent
    exact max_eq_left (by linarith)

end HTGeometry
