import GaloisForLFunctions.HTGeometry.ComplexTorusProductLimit
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Fourier coefficient functionals on the full torus L² space -/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

variable {ι : Type*} [Countable ι]

def torusFourierL2 (n : ι →₀ ℤ) : Lp ℂ 2 (torusHaar ι) →L[ℂ] ℂ :=
  InnerProductSpace.toDual ℂ _ ((torusCharacter n).toLp 2 (torusHaar ι) ℂ)

theorem torusFourierL2_apply (n : ι →₀ ℤ) (f : Lp ℂ 2 (torusHaar ι)) :
    torusFourierL2 n f = ∫ x, conj (torusCharacter n x) * f x ∂torusHaar ι := by
  change inner ℂ ((torusCharacter n).toLp 2 (torusHaar ι) ℂ) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (torusHaar ι) (torusCharacter n)] with x hx
  rw [hx, RCLike.inner_apply']

theorem torusFourierL2_torusFiniteProduct (f : ι → C(UnitAddCircle, ℂ))
    (P : Finset ι) {n : ι →₀ ℤ} (hn : n.support ⊆ P) :
    torusFourierL2 n (torusFiniteProductLp f P) =
      ∏ i ∈ P, ∫ θ, conj (fourier (n i) θ) * f i θ ∂AddCircle.haarAddCircle := by
  rw [torusFourierL2_apply]
  calc
    _ = ∫ x, ∏ i ∈ P, conj (fourier (n i) (x i)) * f i (x i) ∂torusHaar ι := by
      apply integral_congr_ae
      filter_upwards [coeFn_torusFiniteProductLp f P] with x hx
      rw [hx, torusCharacter_apply_of_subset hn]
      change conj (∏ i ∈ P, fourier (n i) (x i)) * (∏ i ∈ P, f i (x i)) = _
      rw [map_prod, Finset.prod_mul_distrib]
    _ = _ := integral_torus_finite_product P
      (fun i θ => conj (fourier (n i) θ) * f i θ) (fun i => by fun_prop)

end

end GaloisForLFunctions.HTGeometry
