/-
The two scale windows of the frontier object are disjoint at every finite degree.

Split the critical sum into blocks of length `N^c`.  Two requirements compete.

**Polynomial approximation.**  The critical phase has `k`-th derivative of size `N/n^k`, so on a block
of length `N^c` its `k`-th Taylor term has size `N·(N^c/N)^k = N^(1 - k(1-c))`.  A degree-`(k-1)`
approximation is legitimate exactly when that term is bounded, i.e. when

    **c ≤ 1 - 1/k.**

Quadratic blocks (`k = 3`, cubic remainder) need `c ≤ 2/3`.

**Completion.**  Completing an exponential sum against a character modulo `m` is productive only when
the modulus is at least the total phase variation.  The frontier object's variation is `F ≍ N`, while
every modulus its arithmetic structure supplies is at most the Farey order `N^c`.  So completion needs

    **c ≥ 1.**

The two windows are disjoint for every finite `k`, separated by exactly `1/k`.  At the campaign's
working scale `c = 1/3` the completion deficit is `N^(2/3)`; at the largest quadratically valid scale
`c = 2/3` it is still `N^(1/3)`.  Completion becomes available only in the limit `k → ∞`, where no
finite-degree approximation exists.

This is the quantitative form of the smooth/multiplicative dichotomy for this object: the smooth
family lives on `c ≤ 1 - 1/k` and the multiplicative family on `c ≥ 1`, and no scale serves both.
-/
import GaloisForLFunctions.HTGeometry.FareyNumeratorSumBarrier

namespace HTGeometry

/-! ### The two windows -/

/-- Exponent of the `k`-th Taylor term of the critical phase on a block of length `N^c`. -/
def taylorTermExponent (k c : ℚ) : ℚ := 1 - k * (1 - c)

/-- Largest block scale at which a degree-`(k-1)` approximation is legitimate. -/
def taylorValidityMax (k : ℚ) : ℚ := 1 - 1 / k

/-- The completion deficit at block scale `c`: phase variation over available modulus. -/
def completionDeficit (c : ℚ) : ℚ := 1 - c

/-- Smallest block scale at which completion is productive. -/
def completionMin : ℚ := 1

/-- **The Taylor term is bounded exactly on the validity window.** -/
theorem taylorTerm_bounded_iff {k c : ℚ} (hk : 0 < k) :
    taylorTermExponent k c ≤ 0 ↔ c ≤ taylorValidityMax k := by
  unfold taylorTermExponent taylorValidityMax
  have hinv : 1 / k * k = 1 := div_mul_cancel₀ _ (ne_of_gt hk)
  constructor
  · intro h
    have hmul : (c + 1 / k) * k ≤ 1 * k := by
      rw [add_mul, hinv]; nlinarith
    have := le_of_mul_le_mul_right hmul hk
    linarith
  · intro h
    have hmul : (c + 1 / k) * k ≤ 1 * k := mul_le_mul_of_nonneg_right (by linarith) hk.le
    rw [add_mul, hinv] at hmul
    nlinarith

/-- **Completion is productive exactly on its own window.** -/
theorem completion_productive_iff (c : ℚ) :
    completionDeficit c ≤ 0 ↔ completionMin ≤ c := by
  unfold completionDeficit completionMin
  constructor <;> intro h <;> linarith

/-- The validity window is strictly below the completion window, for every finite degree. -/
theorem taylorValidityMax_lt_completionMin {k : ℚ} (hk : 0 < k) :
    taylorValidityMax k < completionMin := by
  unfold taylorValidityMax completionMin
  have : 0 < 1 / k := by positivity
  linarith

/-- **The two windows are disjoint.** -/
theorem windows_disjoint {k c : ℚ} (hk : 0 < k) :
    ¬ (c ≤ taylorValidityMax k ∧ completionMin ≤ c) := by
  rintro ⟨h1, h2⟩
  exact absurd (h2.trans h1) (not_le.mpr (taylorValidityMax_lt_completionMin hk))

/-- **The gap between them is exactly `1/k`.** -/
theorem window_gap (k : ℚ) : completionMin - taylorValidityMax k = 1 / k := by
  unfold completionMin taylorValidityMax; ring

/-- **On the validity window the completion deficit is at least `1/k`.** -/
theorem deficit_ge_on_validity_window {k c : ℚ} (h : c ≤ taylorValidityMax k) :
    1 / k ≤ completionDeficit c := by
  unfold completionDeficit taylorValidityMax at *
  linarith

/-! ### The quadratic case -/

/-- Quadratic blocks are legitimate up to `c = 2/3`. -/
@[simp] theorem quadratic_validity : taylorValidityMax 3 = 2 / 3 := by
  unfold taylorValidityMax; norm_num

/-- **At the largest quadratically valid scale the completion deficit is still `1/3`.** -/
theorem quadratic_deficit_at_max : completionDeficit (taylorValidityMax 3) = 1 / 3 := by
  rw [quadratic_validity]; unfold completionDeficit; norm_num

/-- The campaign's working scale, and its deficit. -/
@[simp] theorem working_scale_deficit : completionDeficit (1 / 3) = 2 / 3 := by
  unfold completionDeficit; norm_num

/-- At the working scale the cubic remainder is comfortably negligible. -/
theorem working_scale_cubic : taylorTermExponent 3 (1 / 3) = -1 := by
  unfold taylorTermExponent; norm_num

/-- **The quadratic and completion windows are disjoint with gap `1/3`.** -/
theorem quadratic_windows_disjoint :
    taylorValidityMax 3 < completionMin ∧ completionMin - taylorValidityMax 3 = 1 / 3 := by
  rw [quadratic_validity]
  constructor
  · unfold completionMin; norm_num
  · unfold completionMin; norm_num

/-! ### Higher degrees do not help -/

/-- The validity window grows with the degree. -/
theorem taylorValidityMax_mono {k k' : ℚ} (hk : 0 < k) (h : k < k') :
    taylorValidityMax k < taylorValidityMax k' := by
  unfold taylorValidityMax
  have hk' : 0 < k' := lt_trans hk h
  have : 1 / k' < 1 / k := by
    rw [div_lt_div_iff₀ hk' hk]; linarith
  linarith

/-- **But never reaches the completion window.**  For every finite degree the deficit is a positive
power of `N`, and the deficit shrinks only as `1/k`. -/
theorem no_finite_degree_completes {k : ℚ} (hk : 0 < k) :
    0 < completionDeficit (taylorValidityMax k) ∧
      completionDeficit (taylorValidityMax k) = 1 / k := by
  unfold completionDeficit taylorValidityMax
  constructor
  · have : 0 < 1 / k := by positivity
    linarith
  · ring

/-- **The dichotomy, quantified.**  The smooth family occupies `c ≤ 1 - 1/k` and the multiplicative
family `c ≥ 1`; no scale serves both, at any finite degree. -/
theorem smooth_and_multiplicative_windows_never_meet {k c : ℚ} (hk : 0 < k)
    (hsmooth : taylorTermExponent k c ≤ 0) (hmult : completionDeficit c ≤ 0) : False := by
  rw [taylorTerm_bounded_iff hk] at hsmooth
  rw [completion_productive_iff] at hmult
  exact windows_disjoint hk ⟨hsmooth, hmult⟩

/-- **Uniform closure of the reciprocity route.**  Whatever Farey order is chosen inside the
quadratic window, completion in the numerator carries a deficit of at least `N^(1/3)`. -/
theorem reciprocity_closed_uniformly {c : ℚ} (h : c ≤ taylorValidityMax 3) :
    1 / 3 ≤ completionDeficit c :=
  deficit_ge_on_validity_window (k := 3) h

end HTGeometry
