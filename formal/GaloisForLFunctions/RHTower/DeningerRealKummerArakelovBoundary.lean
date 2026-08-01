import GaloisForLFunctions.RHTower.DeningerRationalPrimeFactorization
import GaloisForLFunctions.RHTower.DeningerEndpointRelativeMiddleReduction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The real Kummer--Arakelov boundary

On real prime coordinates the finite residue trace is `d ↦ ∑_p d_p log p` and the archimedean
Kummer boundary is its negative.  Together they assemble the Arakelov boundary
`d ↦ (d, -∑_p d_p log p)`, which is injective with image the kernel of the Arakelov trace
`(d, x) ↦ ∑_p d_p log p + x`; the trace is surjective, so the cokernel is the orientation line.

On the rational Kummer line the archimedean boundary is `-log|a|`: that is the logarithmic
product formula.

* `deningerFiniteTrace`, `deningerArchBoundary`, `deningerArakelovBoundary`,
  `deningerArakelovTrace` are the maps.
* `deningerArakelovBoundary_injective`, `deningerArakelov_exact`,
  `deningerArakelovTrace_surjective` and `deningerArakelovCokerEquiv` are the endpoint statement.
* `deningerArchBoundary_ratExpReal` is the product formula on the Kummer line, and
  `deningerArchBoundary_abs_le` the continuity bound.
-/

namespace RHTower

section ArakelovBoundary

/-- The logarithm of a natural number is nonnegative. -/
theorem deningerLog_natCast_nonneg (p : ℕ) : 0 ≤ Real.log p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hp)

/-- The finite residue trace `d ↦ ∑_p d_p log p`. -/
noncomputable def deningerFiniteTrace : (ℕ →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun p : ℕ => Real.log p)

theorem deningerFiniteTrace_apply (d : ℕ →₀ ℝ) :
    deningerFiniteTrace d = ∑ p ∈ d.support, d p * Real.log p := by
  rw [deningerFiniteTrace, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun p _ => smul_eq_mul _ _

@[simp] theorem deningerFiniteTrace_single (p : ℕ) (x : ℝ) :
    deningerFiniteTrace (Finsupp.single p x) = x * Real.log p := by
  rw [deningerFiniteTrace, Finsupp.linearCombination_single, smul_eq_mul]

/-- The archimedean Kummer boundary `∂_∞ = -∑_p d_p log p`. -/
noncomputable def deningerArchBoundary : (ℕ →₀ ℝ) →ₗ[ℝ] ℝ := -deningerFiniteTrace

theorem deningerArchBoundary_apply (d : ℕ →₀ ℝ) :
    deningerArchBoundary d = -∑ p ∈ d.support, d p * Real.log p := by
  rw [deningerArchBoundary, LinearMap.neg_apply, deningerFiniteTrace_apply]

/-- The Arakelov boundary `d ↦ (d, -∑_p d_p log p)`. -/
noncomputable def deningerArakelovBoundary : (ℕ →₀ ℝ) →ₗ[ℝ] ((ℕ →₀ ℝ) × ℝ) :=
  LinearMap.prod LinearMap.id deningerArchBoundary

@[simp] theorem deningerArakelovBoundary_apply (d : ℕ →₀ ℝ) :
    deningerArakelovBoundary d = (d, deningerArchBoundary d) := rfl

/-- The Arakelov trace `(d, x) ↦ ∑_p d_p log p + x`. -/
noncomputable def deningerArakelovTrace : ((ℕ →₀ ℝ) × ℝ) →ₗ[ℝ] ℝ :=
  deningerFiniteTrace.comp (LinearMap.fst ℝ (ℕ →₀ ℝ) ℝ) + LinearMap.snd ℝ (ℕ →₀ ℝ) ℝ

@[simp] theorem deningerArakelovTrace_apply (v : (ℕ →₀ ℝ) × ℝ) :
    deningerArakelovTrace v = deningerFiniteTrace v.1 + v.2 := rfl

/-- **Injectivity.**  The Arakelov boundary is injective. -/
theorem deningerArakelovBoundary_injective : Function.Injective deningerArakelovBoundary := by
  intro d e h
  exact congrArg Prod.fst h

/-- **Exactness.**  The image of the Arakelov boundary is the kernel of the Arakelov trace. -/
theorem deningerArakelov_exact :
    Function.Exact deningerArakelovBoundary deningerArakelovTrace := by
  rw [LinearMap.exact_iff]
  ext v
  simp only [LinearMap.mem_ker, deningerArakelovTrace_apply, LinearMap.mem_range]
  constructor
  · intro hv
    exact ⟨v.1, Prod.ext rfl (by
      rw [deningerArakelovBoundary_apply, deningerArchBoundary, LinearMap.neg_apply]
      linarith [hv])⟩
  · rintro ⟨d, rfl⟩
    simp [deningerArchBoundary]

/-- **Surjectivity of the trace.** -/
theorem deningerArakelovTrace_surjective : Function.Surjective deningerArakelovTrace := by
  intro r
  exact ⟨(0, r), by simp⟩

/-- **The Arakelov orientation line.**  The cokernel of the Arakelov boundary is `ℝ(-1)`. -/
noncomputable def deningerArakelovCokerEquiv :
    (((ℕ →₀ ℝ) × ℝ) ⧸ LinearMap.range deningerArakelovBoundary) ≃ₗ[ℝ] ℝ :=
  deningerEndpointH2Equiv deningerArakelovBoundary deningerArakelovTrace
    deningerArakelov_exact deningerArakelovTrace_surjective

theorem deningerArakelovCokerEquiv_mk (v : (ℕ →₀ ℝ) × ℝ) :
    deningerArakelovCokerEquiv (Submodule.Quotient.mk v) = deningerArakelovTrace v := rfl

/-- **Continuity of the archimedean boundary.** -/
theorem deningerArchBoundary_abs_le (d : ℕ →₀ ℝ) :
    |deningerArchBoundary d| ≤ ∑ p ∈ d.support, Real.log p * |d p| := by
  rw [deningerArchBoundary_apply, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [abs_mul, abs_of_nonneg (deningerLog_natCast_nonneg p)]
  ring

end ArakelovBoundary

section RationalKummerLine

/-- Real prime coordinates of a rational number. -/
noncomputable def deningerRatExpReal (q : ℚ) : ℕ →₀ ℝ :=
  (deningerRatExp q).mapRange (fun n : ℤ => (n : ℝ)) (by simp)

@[simp] theorem deningerRatExpReal_apply (q : ℚ) (p : ℕ) :
    deningerRatExpReal q p = ((deningerRatExp q p : ℤ) : ℝ) := rfl

theorem deningerRatExpReal_support (q : ℚ) :
    (deningerRatExpReal q).support = (deningerRatExp q).support :=
  Finsupp.support_mapRange_of_injective (by simp) _ Int.cast_injective

/-- **Product formula on the Kummer line.**  The archimedean boundary of a positive rational is
minus its logarithm. -/
theorem deningerArchBoundary_ratExpReal {q : ℚ} (hq : 0 < q) :
    deningerArchBoundary (deningerRatExpReal q) = -Real.log q := by
  rw [deningerArchBoundary_apply, deningerRatExpReal_support]
  congr 1
  rw [deningerLog_eq_sum hq]
  exact Finset.sum_congr rfl fun p _ => rfl

/-- The finite trace of a positive rational's coordinates is its logarithm. -/
theorem deningerFiniteTrace_ratExpReal {q : ℚ} (hq : 0 < q) :
    deningerFiniteTrace (deningerRatExpReal q) = Real.log q := by
  have h := deningerArchBoundary_ratExpReal hq
  rw [deningerArchBoundary, LinearMap.neg_apply, neg_eq_iff_eq_neg, neg_neg] at h
  exact h

/-- The Arakelov trace annihilates every Arakelov boundary. -/
theorem deningerArakelovTrace_boundary (d : ℕ →₀ ℝ) :
    deningerArakelovTrace (deningerArakelovBoundary d) = 0 := by
  simp [deningerArakelovBoundary_apply, deningerArchBoundary, deningerArakelovTrace_apply]

/-- **Product formula.**  For a positive rational the finite residue trace and the archimedean
boundary cancel. -/
theorem deningerProductFormula {q : ℚ} (hq : 0 < q) :
    deningerFiniteTrace (deningerRatExpReal q)
      + deningerArchBoundary (deningerRatExpReal q) = 0 := by
  rw [deningerFiniteTrace_ratExpReal hq, deningerArchBoundary_ratExpReal hq]
  ring

end RationalKummerLine

end RHTower
