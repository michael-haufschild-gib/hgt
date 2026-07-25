/-
The correlation size exponent is determined, not chosen.

The independent-signs model predicts the `2k`-th moment error from one input: the typical size
`M^{s}` of the correlation error `Δ_k(M,h)`.  The prediction is

    E_k(T)  ≍  T^{1/2} M^{s - 1/2}   at the balanced length `M = T^{k/2}`,
            =  T^{1/2 + k(s - 1/2)/2}.

Demanding the value `T^{k/4}` — which is the *proved* size of `E_k` at both indices where anything is
known, `k = 1` and `k = 2`, each matched by an `Ω`-result — pins `s` uniquely:

    1/2 + k(s - 1/2)/2 = k/4   ⟺   s = 1 - 1/k.

So the size exponent is not a free conjecture: it is forced by the two solved cases.  `1 - 1/k` is
Ivić's size; the constant `1/2` proposed by Conrey and Gonek satisfies the equation only at `k = 2`,
the one index where the two agree.
-/
import GaloisForLFunctions.HTGeometry.IvicSizeCriticality
import GaloisForLFunctions.HTGeometry.MomentResolutionFloor

namespace HTGeometry

/-- Moment-error exponent predicted by the independent-signs model from a correlation size exponent
`s`, at the balanced length `M = T^{k/2}`. -/
noncomputable def modelPrediction (k s : ℝ) : ℝ := 1/2 + k * (s - 1/2) / 2

/-- **The size exponent is uniquely determined by the model's verified output.** -/
theorem modelPrediction_eq_quarter_iff {k s : ℝ} (hk : 0 < k) :
    modelPrediction k s = k/4 ↔ s = 1 - 1/k := by
  unfold modelPrediction
  constructor
  · intro h
    have hk' : k ≠ 0 := ne_of_gt hk
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    subst h
    have hk' : k ≠ 0 := ne_of_gt hk
    field_simp
    ring

/-- At `k = 1` the forced size is `0`: the correlation error for `d₁ ≡ 1` is bounded, and the model
returns `E₁ ≍ T^{1/4}` — the proved value. -/
theorem forcedSize_one : modelPrediction 1 (1 - 1/1) = 1/4 := by
  unfold modelPrediction; norm_num

/-- At `k = 2` the forced size is `1/2`, where Ivić's and Conrey–Gonek's proposals coincide, and the
model returns `E₂ ≍ T^{1/2}` — the proved value. -/
theorem forcedSize_two : modelPrediction 2 (1 - 1/2) = 1/2 := by
  unfold modelPrediction; norm_num

/-- **Conrey–Gonek's constant meets the model only at `k = 2`.**  Taking `s = 1/2` for every `k`
would predict `E_k ≍ T^{1/2}` at every index, which is the correct value only at `k = 2`. -/
theorem conreyGonek_size_fits_only_at_two {k : ℝ} (hk : 0 < k) :
    modelPrediction k (1/2) = k/4 ↔ k = 2 := by
  rw [modelPrediction_eq_quarter_iff hk]
  constructor
  · intro h
    have hk' : k ≠ 0 := ne_of_gt hk
    field_simp at h
    linarith
  · rintro rfl; norm_num

/-- The constant size predicts `T^{1/2}` at every index — in particular at `k = 1`, where the proved
value is `T^{1/4}`. -/
theorem conreyGonek_size_prediction (k : ℝ) : modelPrediction k (1/2) = 1/2 := by
  unfold modelPrediction; norm_num

/-- **The consequence.**  The forced size is Ivić's, and Ivić's size delivers `m(k) = 1` only for
`k ≤ 3`; the additive-divisor route with it is therefore capped.  This is the model's own verdict on
the dichotomy it was built to describe. -/
theorem model_forces_ivic_size {k : ℝ} (hk : 0 < k) :
    (modelPrediction k (ivicSize k) = k/4) ∧
    (transferBound k 1 (ivicSize k) = 1 ↔ k ≤ 3) := by
  refine ⟨?_, ivic_gives_one_iff hk⟩
  rw [modelPrediction_eq_quarter_iff hk]
  rfl

end HTGeometry
