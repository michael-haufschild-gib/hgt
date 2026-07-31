import GaloisForLFunctions.HTGeometry.NestedExhaustionCayleyLimit
import Mathlib.Analysis.Normed.Algebra.Spectrum
import GaloisForLFunctions.HTGeometry.NormalResolventDistance
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Spectral inclusion under strong convergence

Strong convergence transports approximate eigenvectors: if one fixed unit vector nearly solves the
eigenvalue equation for the limit operator, it nearly solves it for every sufficiently late member
of the family.  An approximate eigenvector in turn forces the resolvent norm to be large, because
the resolvent recovers the vector from its own image.

Together these give the spectral inclusion statement of a nested exhaustion: near every spectral
point of the limit, the resolvents of the approximating operators are eventually unbounded, so the
approximating spectra eventually enter every neighbourhood of that point.  Only inclusion of the
target spectrum is obtained; nothing here excludes additional spectral pollution of the
approximants away from the target spectrum.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable {ι : Type*} {l : Filter ι}

/-- **Approximate eigenvectors transfer.**  A vector that nearly solves the eigenvalue equation
for the limit operator nearly solves it for every sufficiently late member of the family. -/
theorem eventually_norm_sub_smul_lt {T : ι → E →L[𝕜] E} {Tinf : E →L[𝕜] E} {μ : 𝕜}
    (h : ∀ x, Tendsto (fun i => T i x) l (𝓝 (Tinf x)))
    {x : E} {ε : ℝ} (hlt : ‖Tinf x - μ • x‖ < ε) :
    ∀ᶠ i in l, ‖T i x - μ • x‖ < ε := by
  have hconv : Tendsto (fun i => ‖T i x - μ • x‖) l (𝓝 ‖Tinf x - μ • x‖) :=
    ((h x).sub (tendsto_const_nhds (x := μ • x))).norm
  exact hconv.eventually (eventually_lt_nhds hlt)

/-- **An approximate eigenvector makes the resolvent large.**  If a unit vector is moved a
distance less than `ε` by `T - μ`, then `μ` is either in the spectrum of `T` or its resolvent has
norm greater than `1/ε`. -/
theorem one_div_lt_norm_resolvent {T : E →L[𝕜] E} {μ : 𝕜} (hμ : μ ∉ spectrum 𝕜 T)
    {x : E} (hx : ‖x‖ = 1) {ε : ℝ} (hε : 0 < ε) (h : ‖T x - μ • x‖ < ε) :
    1 / ε < ‖Ring.inverse (algebraMap 𝕜 (E →L[𝕜] E) μ - T)‖ := by
  set A : E →L[𝕜] E := algebraMap 𝕜 (E →L[𝕜] E) μ - T with hA
  have hunit : IsUnit A := by
    rw [spectrum.notMem_iff] at hμ
    exact hμ
  set S : E →L[𝕜] E := Ring.inverse A with hS
  have hSA : S * A = 1 := by
    rw [hS, Ring.inverse_mul_cancel A hunit]
  have hSAx : S (A x) = x := by
    have := congrArg (fun (f : E →L[𝕜] E) => f x) hSA
    simpa using this
  have hAx : ‖A x‖ < ε := by
    have hval : A x = -(T x - μ • x) := by
      rw [hA]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [hval, norm_neg]
    exact h
  have hone : (1 : ℝ) ≤ ‖S‖ * ‖A x‖ := by
    calc (1 : ℝ) = ‖x‖ := hx.symm
      _ = ‖S (A x)‖ := by rw [hSAx]
      _ ≤ ‖S‖ * ‖A x‖ := ContinuousLinearMap.le_opNorm _ _
  have hSpos : 0 < ‖S‖ := by
    rcases eq_or_lt_of_le (norm_nonneg S) with hzero | hpos
    · exfalso
      rw [← hzero] at hone
      simp at hone
      linarith
    · exact hpos
  rw [div_lt_iff₀ hε]
  nlinarith [hone, norm_nonneg (A x), hSpos]

/-- **Spectral inclusion of a strongly convergent family.**  If a unit vector almost solves the
eigenvalue equation for the limit, then for every sufficiently late member either `μ` lies in its
spectrum or its resolvent at `μ` has norm greater than `1/ε`. -/
theorem eventually_mem_spectrum_or_norm_resolvent_gt {T : ι → E →L[𝕜] E} {Tinf : E →L[𝕜] E}
    {μ : 𝕜} (h : ∀ x, Tendsto (fun i => T i x) l (𝓝 (Tinf x)))
    {x : E} (hx : ‖x‖ = 1) {ε : ℝ} (hε : 0 < ε) (hlt : ‖Tinf x - μ • x‖ < ε) :
    ∀ᶠ i in l, μ ∈ spectrum 𝕜 (T i) ∨
      1 / ε < ‖Ring.inverse (algebraMap 𝕜 (E →L[𝕜] E) μ - T i)‖ := by
  filter_upwards [eventually_norm_sub_smul_lt h hlt] with i hi
  by_cases hmem : μ ∈ spectrum 𝕜 (T i)
  · exact Or.inl hmem
  · exact Or.inr (one_div_lt_norm_resolvent hmem hx hε hi)

/-- **Spectral inclusion.**  If a unit vector almost solves the eigenvalue equation for the limit
of a strongly convergent family of normal operators, then every sufficiently late member of the
family has a spectral point within `ε` of `μ`. -/
theorem eventually_exists_mem_spectrum_norm_sub_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type*} {l : Filter ι}
    {T : ι → E →L[ℂ] E} {Tinf : E →L[ℂ] E} {μ : ℂ}
    (hnormal : ∀ i, IsStarNormal (T i))
    (h : ∀ x, Tendsto (fun i => T i x) l (𝓝 (Tinf x)))
    {x : E} (hx : ‖x‖ = 1) {ε : ℝ} (hε : 0 < ε) (hlt : ‖Tinf x - μ • x‖ < ε) :
    ∀ᶠ i in l, ∃ lam ∈ spectrum ℂ (T i), ‖μ - lam‖ < ε := by
  filter_upwards [eventually_mem_spectrum_or_norm_resolvent_gt (𝕜 := ℂ) h hx hε hlt] with i hi
  rcases hi with hmem | hbig
  · exact ⟨μ, hmem, by simp [hε]⟩
  · by_contra hcon
    push Not at hcon
    have hfar : ∀ lam ∈ spectrum ℂ (T i), ε ≤ ‖μ - lam‖ := by
      intro lam hlam
      exact hcon lam hlam
    have hnotmem : μ ∉ spectrum ℂ (T i) := by
      intro hmem
      have := hfar μ hmem
      simp at this
      linarith
    have hunit : IsUnit ((algebraMap ℂ (E →L[ℂ] E)) μ - T i) := spectrum.notMem_iff.mp hnotmem
    haveI : IsStarNormal (T i) := hnormal i
    have hle := norm_inverse_le_of_spectrum_far (a := T i) hε hfar hunit
    linarith

end GaloisForLFunctions.HTGeometry
