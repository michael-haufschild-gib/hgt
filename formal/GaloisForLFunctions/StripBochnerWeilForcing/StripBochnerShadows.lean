import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryPositivity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurfaceHodgeIndex

/-!
# The Coupled Strip Bochner–Weil Form and Its Three Shadows

On the critical strip, a nonnegative logarithmic frequency family `(wᵢ, λᵢ)` paired against both a
scale aperture `K : ι → ℝ` and a finite tuple of vertical height channels `x, c : Fin n → ℝ` defines
the **coupled strip Bochner–Weil form**

`ℬ(K; x, c) = ∑ⱼ ∑ₖ cⱼ cₖ ∑ᵢ wᵢ Kᵢ cos(λᵢ (xⱼ − xₖ))`.

This single bilinear-quadratic object on `(scale aperture) × (height channels)` specializes to the
three positivity structures governing completed Euler products:

1. **Multi-channel strip positivity (`stripBochnerForm_nonneg`):** For every nonnegative scale
   aperture `Kᵢ ≥ 0` with summable weighted mass `∑ᵢ wᵢ Kᵢ < ∞`, the channel matrix
   `(j, k) ↦ stripKernel w lam K (xⱼ − xₖ)` is positive semidefinite of arbitrary rank `n`.
2. **Boundary multiplicative shadow (`isEvenPosDef_of_stripKernel_tendsto`):** Along any family of
   apertures `K(δ)` (`δ ↓ 0⁺`) whose normalized strip kernels `δ · stripKernel w lam (K δ) u`
   converge pointwise to `D(u)`, multi-channel strip positivity passes directly to positive
   definiteness of the boundary divisor (`IsEvenPosDef D`), recovering `IsBoundaryDivisor.isEvenPosDef`
   when `wᵢ = 1`.
3. **Scaling-surface `κ`-polar Hodge shadow (`polarSurfaceOfPoleBudget`):** At the single origin
   channel (`n = 1`, `x = 0`), adjoining two isotropic polar fibres `(H, V)` of pole budget `κ ∈ ℝ`
   to a symmetric local cycle pairing `L` on `E` forms a polar surface on `E × ℝ × ℝ` whose
   Castelnuovo–Severi defect is identically the `κ`-weighted Weil functional
   `κ (ℓ_H(x) ℓ_V(y) + ℓ_V(x) ℓ_H(y)) − L(x, y)`. Hodge index on this surface is equivalent to
   `κ`-polar dominance over the local strip pairing, and monotonicity in `κ` reflects expansion of
   the pole budget on polar-positive cycles.
-/

noncomputable section

open Finset Filter Topology
open GaloisForLFunctions.MultiplicativePositivityGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace GaloisForLFunctions.StripBochnerWeilForcing

/-! ### 1. The coupled strip Bochner–Weil kernel and multi-channel Gram form -/

/-- The scale-filtered strip kernel associated to weights `w`, frequencies `lam`, and scale aperture
`K`: `∑ᵢ wᵢ Kᵢ cos(λᵢ u)`. -/
def stripKernel {ι : Type*} (w lam K : ι → ℝ) (u : ℝ) : ℝ :=
  cosineTrace (fun i => w i * K i) lam u

/-- The coupled strip Bochner–Weil quadratic form on `n` height channels `x : Fin n → ℝ` with
channel weights `c : Fin n → ℝ`. -/
def stripBochnerForm {ι : Type*} (w lam K : ι → ℝ) {n : ℕ} (x c : Fin n → ℝ) : ℝ :=
  ∑ j, ∑ k, c j * c k * stripKernel w lam K (x j - x k)

theorem stripKernel_neg {ι : Type*} (w lam K : ι → ℝ) (u : ℝ) :
    stripKernel w lam K (-u) = stripKernel w lam K u :=
  cosineTrace_neg (fun i => w i * K i) lam u

theorem isEvenPosDef_stripKernel {ι : Type*} {w K : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hK : ∀ i, 0 ≤ K i)
    (hs : Summable (fun i => w i * K i)) (lam : ι → ℝ) :
    IsEvenPosDef (stripKernel w lam K) :=
  isEvenPosDef_cosineTrace (fun i => mul_nonneg (hw i) (hK i)) hs lam

/-- **Multi-channel strip Bochner positivity.** Whenever the logarithmic weights `w` and scale
aperture `K` are nonnegative and `w · K` is summable, the coupled strip Bochner–Weil form is
nonnegative across every finite configuration of height channels and channel weights. -/
theorem stripBochnerForm_nonneg {ι : Type*} {w K : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hK : ∀ i, 0 ≤ K i)
    (hs : Summable (fun i => w i * K i)) (lam : ι → ℝ)
    {n : ℕ} (x c : Fin n → ℝ) :
    0 ≤ stripBochnerForm w lam K x c :=
  (isEvenPosDef_stripKernel hw hK hs lam).posDef n x c

/-- Frequencywise spectral identity for the coupled strip Bochner–Weil form: each frequency `λᵢ`
contributes `wᵢ Kᵢ ((∑ⱼ cⱼ cos(λᵢ xⱼ))² + (∑ⱼ cⱼ sin(λᵢ xⱼ))²)`. -/
theorem hasSum_stripBochnerForm {ι : Type*} {w K : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hK : ∀ i, 0 ≤ K i)
    (hs : Summable (fun i => w i * K i)) (lam : ι → ℝ)
    {n : ℕ} (x c : Fin n → ℝ) :
    HasSum
      (fun i => w i * K i *
        ((∑ j, c j * Real.cos (lam i * x j)) ^ 2 + (∑ j, c j * Real.sin (lam i * x j)) ^ 2))
      (stripBochnerForm w lam K x c) := by
  have hwK : ∀ i, 0 ≤ w i * K i := fun i => mul_nonneg (hw i) (hK i)
  have hall : HasSum
      (fun i => ∑ j, ∑ k, c j * c k * (w i * K i * Real.cos (lam i * (x j - x k))))
      (stripBochnerForm w lam K x c) :=
    hasSum_sum fun j _ => hasSum_sum fun k _ =>
      ((summable_cosineTrace_terms hwK hs lam (x j - x k)).hasSum).mul_left _
  refine hall.congr_fun fun i => ?_
  have hpull : ∑ j, ∑ k, c j * c k * (w i * K i * Real.cos (lam i * (x j - x k))) =
      w i * K i * ∑ j, ∑ k, c j * c k * Real.cos (lam i * (x j - x k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hpull, gram_cos_eq]

/-! ### 2. Boundary multiplicative shadow (`δ ↓ 0⁺`) -/

/-- **Boundary shadow specialization.** Along any family of nonnegative scale apertures `K δ`
(`δ > 0`) whose normalized strip kernels `δ · stripKernel w lam (K δ) u` converge pointwise to `D u`
as `δ ↓ 0⁺`, the limit `D` is an even positive-definite boundary divisor on `ℝ`. -/
theorem isEvenPosDef_of_stripKernel_tendsto {ι : Type*} {w : ι → ℝ} {K : ℝ → ι → ℝ}
    {lam : ι → ℝ} {D : ℝ → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hK : ∀ δ, 0 < δ → ∀ i, 0 ≤ K δ i)
    (hs : ∀ δ, 0 < δ → Summable (fun i => w i * K δ i))
    (htend : ∀ u, Tendsto (fun δ => δ * stripKernel w lam (K δ) u) (𝓝[>] 0) (𝓝 (D u))) :
    IsEvenPosDef D :=
  isEvenPosDef_of_tendsto (l := 𝓝[>] (0 : ℝ))
    (F := fun δ u => δ * stripKernel w lam (K δ) u)
    (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (isEvenPosDef_stripKernel hw (hK δ hδ) (hs δ hδ) lam).smul (le_of_lt hδ))
    htend

/-- Every `IsBoundaryDivisor` datum arises as the unit-weight (`w = 1`) specialization of the strip
Bochner–Weil kernel along `δ ↓ 0⁺`. -/
theorem stripKernel_recovers_boundaryDivisor {ι : Type*} {lam : ι → ℝ} {K : ℝ → ι → ℝ}
    {D : ℝ → ℝ} (hD : IsBoundaryDivisor lam K D) :
    (∀ δ u, stripKernel (fun _ => 1) lam (K δ) u = cosineTrace (K δ) lam u) ∧ IsEvenPosDef D := by
  refine ⟨fun δ u => ?_, ?_⟩
  · simp only [stripKernel, one_mul]
  · exact isEvenPosDef_of_stripKernel_tendsto (w := fun _ => 1)
      (fun _ => zero_le_one) hD.nonneg
      (fun δ hδ => by simpa only [one_mul] using hD.summable δ hδ)
      (fun u => by simpa only [stripKernel, one_mul] using hD.tendsto u)

/-! ### 3. Scaling-surface `κ`-polar Hodge shadow (`n = 1` origin channel) -/

/-- The `κ`-pole-graded intersection pairing on `E × (ℝ × ℝ)` extending a symmetric local strip
pairing `L` on `E` by two isotropic polar fibre classes `(0, 1, 0)` and `(0, 0, 1)` coupled to `E`
through linear pole functionals `ℓ_H, ℓ_V` with pole budget `κ ∈ ℝ`. -/
def poleGradedPair {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ℓH ℓV : E →ₗ[ℝ] ℝ) (κ : ℝ) :
    (E × (ℝ × ℝ)) →ₗ[ℝ] (E × (ℝ × ℝ)) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun p q =>
      L p.1 q.1 + p.2.1 * q.2.2 + p.2.2 * q.2.1 +
        q.2.2 * ℓH p.1 + p.2.2 * ℓH q.1 + κ * q.2.1 * ℓV p.1 + κ * p.2.1 * ℓV q.1)
    (fun p₁ p₂ q => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (fun c p q => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun p q₁ q₂ => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun c p q => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
      ring)

/-- **The `κ`-graded polar surface.** Adjoining the two isotropic polar fibres to `(E, L, ℓ_H, ℓ_V)`
with pole weight `κ` forms a `PolarSurface` on `E × (ℝ × ℝ)` for every `κ ∈ ℝ`. -/
def polarSurfaceOfPoleBudget {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hL : ∀ x y, L x y = L y x)
    (ℓH ℓV : E →ₗ[ℝ] ℝ) (κ : ℝ) :
    PolarSurface (E × (ℝ × ℝ)) where
  pair := poleGradedPair L ℓH ℓV κ
  pair_comm p q := by
    simp only [poleGradedPair, LinearMap.mk₂_apply, hL p.1 q.1]
    ring
  H := (0, (1, 0))
  V := (0, (0, 1))
  pair_H_H := by simp [poleGradedPair]
  pair_V_V := by simp [poleGradedPair]
  pair_H_V := by simp [poleGradedPair]

/-- **Exact defect law on the `κ`-graded polar surface.** On all of `E × (ℝ × ℝ)`, the
Castelnuovo–Severi defect depends only on the cycle projection in `E` and equals the `κ`-weighted
Weil functional `κ (ℓ_H(x) ℓ_V(y) + ℓ_V(x) ℓ_H(y)) − L(x, y)`. -/
theorem defect_polarSurfaceOfPoleBudget {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hL : ∀ x y, L x y = L y x)
    (ℓH ℓV : E →ₗ[ℝ] ℝ) (κ : ℝ) (p q : E × (ℝ × ℝ)) :
    (polarSurfaceOfPoleBudget L hL ℓH ℓV κ).defect p q =
      κ * (ℓH p.1 * ℓV q.1 + ℓV p.1 * ℓH q.1) - L p.1 q.1 := by
  simp only [PolarSurface.defect, PolarSurface.polar, polarSurfaceOfPoleBudget, poleGradedPair,
    LinearMap.mk₂_apply, map_zero]
  ring

/-- **Hodge index equivalence for pole budget `κ`.** The `κ`-graded polar surface satisfies the
Hodge index theorem if and only if the single-channel local strip pairing satisfies the `κ`-pole
bound `L(x, x) ≤ 2 κ ℓ_H(x) ℓ_V(x)` for every scale cycle `x ∈ E`. -/
theorem hodgeIndex_polarSurfaceOfPoleBudget_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hL : ∀ x y, L x y = L y x)
    (ℓH ℓV : E →ₗ[ℝ] ℝ) (κ : ℝ) :
    (polarSurfaceOfPoleBudget L hL ℓH ℓV κ).HodgeIndex ↔
      ∀ x : E, L x x ≤ 2 * κ * ℓH x * ℓV x := by
  rw [PolarSurface.hodgeIndex_iff_castelnuovoSeveri, PolarSurface.castelnuovoSeveri_iff_defect_nonneg]
  constructor
  · intro h x
    have hx := h (x, (0, 0))
    rw [defect_polarSurfaceOfPoleBudget] at hx
    linarith
  · intro h p
    rw [defect_polarSurfaceOfPoleBudget]
    have hx := h p.1
    linarith

/-- **Zero-pole collapse on a Bochner-positive local pairing.** When the single-channel local strip
pairing is positive semidefinite (`0 ≤ L x x`) and the pole budget is `κ = 0`, Hodge index forces
the local pairing to vanish identically on the diagonal. -/
theorem local_diag_eq_zero_of_hodgeIndex_pole_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hL : ∀ x y, L x y = L y x)
    (hLpos : ∀ x, 0 ≤ L x x) (ℓH ℓV : E →ₗ[ℝ] ℝ)
    (hHodge : (polarSurfaceOfPoleBudget L hL ℓH ℓV 0).HodgeIndex) (x : E) :
    L x x = 0 := by
  have hle := (hodgeIndex_polarSurfaceOfPoleBudget_iff L hL ℓH ℓV 0).mp hHodge x
  linarith [hLpos x]

/-- **Pole-budget monotonicity of the Castelnuovo–Severi defect.** Increasing the pole budget from
`κ₁` to `κ₂ ≥ κ₁` increases the self-defect on every polar-aligned cycle (`0 ≤ ℓ_H(x) ℓ_V(x)`). -/
theorem defect_mono_poleBudget {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hL : ∀ x y, L x y = L y x)
    (ℓH ℓV : E →ₗ[ℝ] ℝ) {κ₁ κ₂ : ℝ} (hκ : κ₁ ≤ κ₂)
    (p : E × (ℝ × ℝ)) (hpol : 0 ≤ ℓH p.1 * ℓV p.1) :
    (polarSurfaceOfPoleBudget L hL ℓH ℓV κ₁).defect p p ≤
      (polarSurfaceOfPoleBudget L hL ℓH ℓV κ₂).defect p p := by
  rw [defect_polarSurfaceOfPoleBudget, defect_polarSurfaceOfPoleBudget]
  nlinarith

end GaloisForLFunctions.StripBochnerWeilForcing
