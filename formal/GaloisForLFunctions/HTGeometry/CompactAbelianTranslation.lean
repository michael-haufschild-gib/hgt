import GaloisForLFunctions.HTGeometry.CompactAbelianConvSymmetric

/-!
# Translation on `L²` and its commutation with convolution

Translation by a group element is an isometry of `L²(G)`, because Haar measure is invariant, and it
commutes with convolution, because convolution is itself built from translation.  Consequently every
eigenspace of a convolution operator is translation invariant — the point at which the finite
dimensionality supplied by compactness turns into characters.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
theorem measurePreserving_translate (a : G) :
    MeasurePreserving (fun x : G => x + a) (haarProb G) (haarProb G) :=
  measurePreserving_add_right (haarProb G) a

/-- Translation of an `L²` function. -/
def transLM (a : G) : Lp ℂ 2 (haarProb G) →ₗ[ℂ] Lp ℂ 2 (haarProb G) where
  toFun := Lp.compMeasurePreserving (fun x : G => x + a) (measurePreserving_translate a)
  map_add' u v := map_add _ u v
  map_smul' c u := by
    refine Lp.ext ?_
    have h1 := Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) (c • u)
      (measurePreserving_translate a)
    have h2 := Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) u (measurePreserving_translate a)
    have h3 : (fun x : G => (c • u) x) =ᵐ[haarProb G] fun x => c • u x := Lp.coeFn_smul c u
    have h4 := (measurePreserving_translate (G := G) a).quasiMeasurePreserving.ae_eq_comp h3
    have h5 := Lp.coeFn_smul c
      (Lp.compMeasurePreserving (fun x : G => x + a) (measurePreserving_translate a) u)
    filter_upwards [h1, h2, h4, h5] with x hx1 hx2 hx4 hx5
    simp only [Function.comp_apply, RingHom.id_apply, Pi.smul_apply] at hx1 hx2 hx4 hx5 ⊢
    rw [hx1, hx4, hx5, hx2]

omit [T2Space G] in
theorem transLM_coeFn (a : G) (u : Lp ℂ 2 (haarProb G)) :
    (fun x => (transLM a u) x) =ᵐ[haarProb G] fun x => u (x + a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_translate a)

omit [T2Space G] in
theorem norm_transLM (a : G) (u : Lp ℂ 2 (haarProb G)) : ‖transLM a u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (measurePreserving_translate a)

/-- Translation as a continuous linear operator on `L²`. -/
def transOp (a : G) : Lp ℂ 2 (haarProb G) →L[ℂ] Lp ℂ 2 (haarProb G) :=
  LinearMap.mkContinuous (transLM a) 1 fun u => by simpa using (norm_transLM a u).le

omit [T2Space G] in
@[simp] theorem transOp_apply (a : G) (u : Lp ℂ 2 (haarProb G)) : transOp a u = transLM a u := rfl

omit [T2Space G] in
theorem transOp_coeFn (a : G) (u : Lp ℂ 2 (haarProb G)) :
    (fun x => (transOp a u) x) =ᵐ[haarProb G] fun x => u (x + a) := transLM_coeFn a u

omit [T2Space G] in
theorem norm_transOp (a : G) (u : Lp ℂ 2 (haarProb G)) : ‖transOp a u‖ = ‖u‖ := norm_transLM a u

variable (k : G → ℂ) (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)

omit [T2Space G] in
/-- Convolution of a translate is the translate of the convolution, pointwise in the continuous
representative. -/
theorem convFun_transOp (a : G) (u : Lp ℂ 2 (haarProb G)) (x : G) :
    convFun k (fun y => (transOp a u) y) x = convFun k (fun y => u y) (x + a) := by
  have h1 : convFun k (fun y => (transOp a u) y) x
      = ∫ y, (u (y + a)) * k (x - y) ∂(haarProb G) := by
    refine integral_congr_ae ?_
    filter_upwards [transOp_coeFn a u] with y hy
    show ((transOp a u : Lp ℂ 2 (haarProb G)) : G → ℂ) y * k (x - y)
        = ((u : Lp ℂ 2 (haarProb G)) : G → ℂ) (y + a) * k (x - y)
    rw [hy]
  have h2 : ∫ y, (u (y + a)) * k (x - y) ∂(haarProb G)
      = ∫ y, (u y) * k (x + a - y) ∂(haarProb G) := by
    have h := integral_add_right (fun y : G => (u y) * k (x + a - y)) a
    refine Eq.trans ?_ h
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hxy : x + a - (y + a) = x - y := by abel
    show (u : G → ℂ) (y + a) * k (x - y) = (u : G → ℂ) (y + a) * k (x + a - (y + a))
    rw [hxy]
  rw [h1, h2]
  rfl

omit [T2Space G] in
include hk hC in
/-- **Convolution commutes with translation.** -/
theorem convOp_transOp (a : G) (u : Lp ℂ 2 (haarProb G)) :
    convOp k hk hC (transOp a u) = transOp a (convOp k hk hC u) := by
  refine Lp.ext ?_
  have hL := convOp_coeFn k hk hC (transOp a u)
  have hR := transOp_coeFn a (convOp k hk hC u)
  have hRR : (fun x : G => (convOp k hk hC u) (x + a))
      =ᵐ[haarProb G] fun x : G => convC k hk hC u (x + a) :=
    (measurePreserving_translate (G := G) a).quasiMeasurePreserving.ae_eq_comp
      (convOp_coeFn k hk hC u)
  filter_upwards [hL, hR, hRR] with x hx hx2 hx3
  rw [hx, hx2, hx3]
  exact convFun_transOp k a u x

end

end CompactAbelian

end GaloisForLFunctions
