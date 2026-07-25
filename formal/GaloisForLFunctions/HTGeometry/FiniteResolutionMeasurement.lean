import GaloisForLFunctions.HTGeometry.InjectivityModulusStability

/-!
# Finite-resolution measurement theorem

The concrete measurement theorem of `wigner-smith-finite-resolution-law-escape` `(15)-(18)`: a finite
law window with monomial exponents `e` is measured at `m` center energies through the jet values
`y j i = f^{(i)}(E_j)`.  The resulting measurement operator `measCLM e y` on the coefficient space is a
continuous linear map depending continuously on `y`, so — via the injectivity-modulus law escape
(`injMod_eventually_pos`) — injectivity at the true hypertranscendental jet `y₀` propagates to a
positive least singular value at every sufficiently fine finite resolution `y x → y₀`.  This is the
deterministic noise margin `(14)`/`(18)`, formalized unconditionally.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Finite measurement operator on the coefficient space `(Fin N → ℝ)` of a law window with monomial
exponents `e`, evaluated at the `m` jet-sample points `y j : Fin n → ℝ`: the matrix action
`c ↦ (∑ k, c k · ∏ i (y j i)^(e k i))_j`, packaged as a continuous linear map. -/
noncomputable def measCLM {n m N : ℕ} (e : Fin N → (Fin n → ℕ)) (y : Fin m → Fin n → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ∑ k : Fin N, (ContinuousLinearMap.proj k).smulRight (fun j => ∏ i, (y j i) ^ (e k i))

/-- The measurement operator depends continuously on the jet-sample values `y`: each entry is a
monomial in the finitely many sampled jet coordinates. -/
theorem continuous_measCLM {n m N : ℕ} (e : Fin N → (Fin n → ℕ)) :
    Continuous (fun y : Fin m → Fin n → ℝ => measCLM e y) := by
  apply continuous_finsetSum
  intro k _
  refine (ContinuousLinearMap.smulRightL ℝ (Fin N → ℝ) (Fin m → ℝ)
    (ContinuousLinearMap.proj k)).continuous.comp ?_
  apply continuous_pi
  intro j
  apply continuous_finsetProd
  intro i _
  exact ((continuous_apply i).comp (continuous_apply j)).pow _

/-- **Finite-resolution measurement theorem.**  If the measurement operator is injective at a jet
value `y₀` (the sampled hypertranscendental law admits no coefficient-normalized fit) and the sampled
jet values converge, `y x → y₀`, then the measurement operator is eventually injective with a strictly
positive least singular value: every sufficiently fine finite-resolution measurement robustly excludes
every nonzero law in the window. -/
theorem measCLM_eventually_injMod_pos {n m N : ℕ} [Nonempty (Fin N)]
    (e : Fin N → (Fin n → ℕ)) {y₀ : Fin m → Fin n → ℝ}
    (hinj : Function.Injective (measCLM e y₀))
    {ι : Type*} {l : Filter ι} {y : ι → (Fin m → Fin n → ℝ)} (hy : Tendsto y l (𝓝 y₀)) :
    ∀ᶠ x in l, 0 < injMod (measCLM e (y x)) :=
  injMod_eventually_pos hinj (((continuous_measCLM e).tendsto y₀).comp hy)

end GaloisForLFunctions.HTGeometry
