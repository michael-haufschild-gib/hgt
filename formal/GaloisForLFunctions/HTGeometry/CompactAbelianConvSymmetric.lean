import GaloisForLFunctions.HTGeometry.CompactAbelianConvCompact

/-!
# Convolution with a Hermitian kernel is a symmetric operator

For a kernel with `conj (k (-z)) = k z` the convolution operator on `L²(G)` is symmetric: both
`⟪k * u, v⟫` and `⟪u, k * v⟫` are the same double integral, and the two orders of integration agree
by Fubini, the integrand being dominated by `‖k‖_∞ |u| |v|` on the product.

Together with compactness this puts the spectral theorem for compact self-adjoint operators at the
disposal of harmonic analysis on the phase carrier.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

omit [T2Space G] [SecondCountableTopology G] in
theorem inner_lp_eq (f g : Lp ℂ 2 (haarProb G)) :
    inner ℂ f g = ∫ a, (starRingEnd ℂ) (f a) * g a ∂(haarProb G) := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => RCLike.inner_apply' _ _)

variable (k : G → ℂ) (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)

omit [T2Space G] in
include hk hC in
theorem integrable_uncurry_kernel (u v : Lp ℂ 2 (haarProb G)) :
    Integrable (Function.uncurry fun x y : G =>
      (starRingEnd ℂ) (u y) * (starRingEnd ℂ) (k (x - y)) * v x)
      ((haarProb G).prod (haarProb G)) := by
  have hu : Integrable (fun y => (starRingEnd ℂ) (u y)) (haarProb G) :=
    (integrable_lp u).norm.mono'
      (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
      (Filter.Eventually.of_forall fun y => by rw [RCLike.norm_conj])
  have h1 : Integrable (fun z : G × G => v z.1 * (starRingEnd ℂ) (u z.2))
      ((haarProb G).prod (haarProb G)) := (integrable_lp v).mul_prod hu
  have hmeas : AEStronglyMeasurable
      (fun z : G × G => (starRingEnd ℂ) (k (z.1 - z.2))) ((haarProb G).prod (haarProb G)) :=
    (Complex.continuous_conj.comp (hk.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable
  have h2 : Integrable (fun z : G × G =>
      (starRingEnd ℂ) (k (z.1 - z.2)) * (v z.1 * (starRingEnd ℂ) (u z.2)))
      ((haarProb G).prod (haarProb G)) := by
    refine h1.bdd_mul (c := C) hmeas (Filter.Eventually.of_forall fun z => ?_)
    rw [RCLike.norm_conj]
    exact hC _
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  show (starRingEnd ℂ) (k (z.1 - z.2)) * (v z.1 * (starRingEnd ℂ) (u z.2))
      = (starRingEnd ℂ) (u z.2) * (starRingEnd ℂ) (k (z.1 - z.2)) * v z.1
  ring

omit [T2Space G] in
include hk hC in
/-- **A Hermitian kernel gives a symmetric convolution operator.** -/
theorem isSymmetric_convOp (hstar : ∀ z : G, (starRingEnd ℂ) (k (-z)) = k z) :
    LinearMap.IsSymmetric (convOp k hk hC).toLinearMap := by
  intro u v
  have hkey : ∀ x y : G, (starRingEnd ℂ) (k (x - y)) = k (y - x) := by
    intro x y
    have := hstar (y - x)
    rwa [neg_sub] at this
  -- the left inner product as a double integral
  have hL : inner ℂ (convOp k hk hC u) v
      = ∫ x, ∫ y, ((starRingEnd ℂ) (u y) * (starRingEnd ℂ) (k (x - y)) * v x) ∂(haarProb G)
          ∂(haarProb G) := by
    rw [inner_lp_eq]
    refine integral_congr_ae ?_
    filter_upwards [convOp_coeFn k hk hC u] with x hx
    rw [hx]
    have hconj : (starRingEnd ℂ) (convC k hk hC u x)
        = ∫ y, ((starRingEnd ℂ) (u y) * (starRingEnd ℂ) (k (x - y))) ∂(haarProb G) := by
      rw [convC_apply, convFun, ← integral_conj]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => map_mul _ _ _)
    rw [hconj, ← integral_mul_const]
  -- the right inner product as the same double integral, in the other order
  have hR : inner ℂ u (convOp k hk hC v)
      = ∫ y, ∫ x, ((starRingEnd ℂ) (u y) * (starRingEnd ℂ) (k (x - y)) * v x) ∂(haarProb G)
          ∂(haarProb G) := by
    rw [inner_lp_eq]
    refine integral_congr_ae ?_
    filter_upwards [convOp_coeFn k hk hC v] with y hy
    rw [hy, convC_apply, convFun, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (starRingEnd ℂ) ((u : G → ℂ) y) * ((v : G → ℂ) x * k (y - x))
        = (starRingEnd ℂ) ((u : G → ℂ) y) * (starRingEnd ℂ) (k (x - y)) * (v : G → ℂ) x
    rw [hkey x y]
    ring
  show inner ℂ ((convOp k hk hC) u) v = inner ℂ u ((convOp k hk hC) v)
  rw [hL, hR]
  exact integral_integral_swap (integrable_uncurry_kernel k hk hC u v)

end

end CompactAbelian

end GaloisForLFunctions
