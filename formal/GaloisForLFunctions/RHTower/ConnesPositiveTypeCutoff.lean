import Mathlib

/-!
# Positivity of Connes' cut-off distribution `Δ_Λ` (§VIII (23)-(25))

Formalization of the positivity step (23)-(25) inside the proof of Theorem 5 of §VIII of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes derives the Riemann Hypothesis (for all Grössencharakters) from the trace formula by showing
that the Weil distribution is of positive type.  The mechanism is:

* the periodization `E` carries the cut-off subspace `B_{Λ,0}` into the module window `S_Λ`,
  hence the transported projection satisfies `Q'_{Λ,0} ≤ S_Λ`;                        (23)
* therefore `Δ_Λ(f) = Trace((S_Λ - Q'_{Λ,0}) V(f))` is of positive type,               (24)(25)
  because `V(f ∗ f^*) = V(f) V(f)^*` and `Trace(R V(f) V(f)^*) = Trace(V(f)^* R V(f)) ≥ 0` for
  `R ≥ 0`;
* letting `Λ → ∞` and using a) gives positivity of the Weil distribution `Δ`, i.e. RH.

The two structural ingredients are proved here without hypotheses:

* `connes_starProjection_norm_mono` - (23): the orthogonal projection onto a smaller closed
  subspace has smaller norm at every vector, i.e. `P_K ≤ P_L` as quadratic forms when `K ≤ L`.
* `connes_positiveType_conjugate` - (25): a positive linear functional on a C*-algebra is
  nonnegative on every conjugate `a^* r a` of a positive element, which is exactly the positivity
  of `Δ_Λ` on `f ∗ f^*` once (23) provides `R = S_Λ - Q'_{Λ,0} ≥ 0`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open Submodule

/-- **§VIII (23).**  If `K ≤ L` are closed subspaces then `‖P_K x‖ ≤ ‖P_L x‖` for every `x`;
equivalently `P_K ≤ P_L` as quadratic forms. -/
theorem connes_starProjection_norm_mono {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {K L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (hKL : K ≤ L) (x : E) :
    ‖K.starProjection x‖ ≤ ‖L.starProjection x‖ := by
  have hcomp := Submodule.starProjection_comp_starProjection_of_le (𝕜 := 𝕜) hKL
  have hx : K.starProjection x = K.starProjection (L.starProjection x) := by
    conv_lhs => rw [← hcomp]
    rfl
  rw [hx]
  exact K.norm_starProjection_apply_le _

/-- **§VIII (25).**  A positive linear functional on a C*-algebra is nonnegative on `a^* r a` for
every positive `r`; with `r = S_Λ - Q'_{Λ,0}` and `a = V(f)` this is exactly
`Δ_Λ(f ∗ f^*) ≥ 0`. -/
theorem connes_positiveType_conjugate {A : Type*} [NonUnitalRing A] [PartialOrder A]
    [StarRing A] [StarOrderedRing A] {τ : A →+ ℝ} (hτ : ∀ b : A, 0 ≤ b → 0 ≤ τ b)
    {r : A} (hr : 0 ≤ r) (a : A) : 0 ≤ τ (star a * r * a) :=
  hτ _ (star_left_conjugate_nonneg hr a)

end

end GaloisForLFunctions.RHTower
