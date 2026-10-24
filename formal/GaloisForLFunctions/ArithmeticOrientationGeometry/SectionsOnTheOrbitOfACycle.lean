import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SectionEffectivityAndTheUniversalFloorLaw

/-!
# Sections on the orbit of a cycle

What is an arithmetic section of a cycle, and why would it satisfy Riemann–Roch without reference
to the sign of Weil's form? Arithmetic Castelnuovo–Severi shows that on any polar surface every
ample cone of nonnegative degree satisfies Riemann–Roch iff it contains the open positive cone and
the defect is nonnegative everywhere (the universal floor law,
`riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg`). AOG localizes this to one orbit.

* **The orbit surface** (`orbitSurface`). When the scales act on the fibre classes by the scalars
  `e^{±s/2}` (`FibreCompatible`, true for `ℤ` and for every configuration), the span of `H, V` and
  the orbit `{ψ_g x}` is stable under every scale (`map_act_orbitSpan_le`), and the pairing
  restricts to a polar surface on it (`PolarSurface.restrict`). Every element of the orbit span is
  a pole-plane class plus the action of a correspondence (`exists_eq_corr_of_mem_orbitSpan`), so
  the defect is nonnegative on the orbit surface iff `x` has the orbit Hodge index
  (`orbitSurface_defect_nonneg_iff`).
* **Riemann–Roch on an orbit is orientation** (`orbitSurface_riemannRoch_iff`). For every set `E` of
  classes of the orbit surface with nonnegative ample degree and the ample axiom: `E` satisfies
  Riemann–Roch iff it contains the open positive cone and `x` is oriented. A section theory of an
  orbit has Riemann–Roch exactly when the orbit is oriented; Riemann–Roch is never an input
  independent of the sign.
* **On a configuration** (`configOrbitSurface_riemannRoch_iff_blind`): on a symmetric tempered
  configuration, Riemann–Roch on the orbit surface of `x` is blindness of `x` to the off-line
  zeros. Sections with Riemann–Roch exist exactly over the oriented locus.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- The restriction of a polar surface to a submodule containing the fibre classes. -/
def restrict (W : Submodule ℝ E) (hH : S.H ∈ W) (hV : S.V ∈ W) : PolarSurface W where
  pair := S.pair.compl₁₂ W.subtype W.subtype
  pair_comm x y := S.pair_comm x y
  H := ⟨S.H, hH⟩
  V := ⟨S.V, hV⟩
  pair_H_H := S.pair_H_H
  pair_V_V := S.pair_V_V
  pair_H_V := S.pair_H_V

theorem restrict_pair (W : Submodule ℝ E) (hH : S.H ∈ W) (hV : S.V ∈ W) (x y : W) :
    (S.restrict W hH hV).pair x y = S.pair x y := rfl

theorem restrict_defect (W : Submodule ℝ E) (hH : S.H ∈ W) (hV : S.V ∈ W) (x y : W) :
    (S.restrict W hH hV).defect x y = S.defect x y := rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

namespace ScalingDatum

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ScalingDatum G E)

/-- The scales act on the fibre classes by the scalars `e^{±s/2}`. -/
def FibreCompatible : Prop :=
  ∀ g, D.act g D.H = Real.exp (D.scale g / 2) • D.H ∧ D.act g D.V = Real.exp (-D.scale g / 2) • D.V

/-- The span of the fibre classes and the orbit of `x`. -/
def orbitSpan (x : E) : Submodule ℝ E :=
  Submodule.span ℝ ({D.H, D.V} ∪ Set.range fun g : G => D.act g x)

theorem H_mem_orbitSpan (x : E) : D.H ∈ D.orbitSpan x :=
  Submodule.subset_span (Or.inl (Or.inl rfl))

theorem V_mem_orbitSpan (x : E) : D.V ∈ D.orbitSpan x :=
  Submodule.subset_span (Or.inl (Or.inr rfl))

theorem orbit_mem_orbitSpan (x : E) (g : G) : D.act g x ∈ D.orbitSpan x :=
  Submodule.subset_span (Or.inr ⟨g, rfl⟩)

/-- **The orbit span is stable under every scale.** -/
theorem map_act_orbitSpan_le (hF : D.FibreCompatible) (x : E) (g : G) :
    (D.orbitSpan x).map (D.act g) ≤ D.orbitSpan x := by
  rw [orbitSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with (rfl | rfl) | ⟨h, rfl⟩
  · rw [(hF g).1]; exact Submodule.smul_mem _ _ (D.H_mem_orbitSpan x)
  · rw [(hF g).2]; exact Submodule.smul_mem _ _ (D.V_mem_orbitSpan x)
  · show D.act g (D.act h x) ∈ D.orbitSpan x
    rw [← D.act_add]; exact D.orbit_mem_orbitSpan x _

theorem act_mem_orbitSpan (hF : D.FibreCompatible) (x : E) (g : G) {w : E}
    (hw : w ∈ D.orbitSpan x) : D.act g w ∈ D.orbitSpan x :=
  D.map_act_orbitSpan_le hF x g ⟨w, hw, rfl⟩

/-- The **orbit surface** of `x`: the polar surface on the span of `H, V` and the orbit of `x`. -/
def orbitSurface (x : E) : PolarSurface (D.orbitSpan x) :=
  D.toPolarSurface.restrict (D.orbitSpan x) (D.H_mem_orbitSpan x) (D.V_mem_orbitSpan x)

theorem corr_smul (c : ℝ) (ξ : Correspondence G) (x : E) : D.corr (c • ξ) x = c • D.corr ξ x := by
  simp only [corr]
  rw [Finsupp.sum_smul_index' (fun _ => zero_smul ℝ _), Finsupp.smul_sum]
  simp only [smul_smul]

/-- Every element of the span of the orbit is the action of a correspondence. -/
theorem exists_corr_of_mem_span_orbit (x : E) {w : E}
    (hw : w ∈ Submodule.span ℝ (Set.range fun g : G => D.act g x)) :
    ∃ ξ : Correspondence G, w = D.corr ξ x := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact ⟨Finsupp.single g 1, by rw [D.corr_single, one_smul]⟩
  | zero => exact ⟨0, (D.corr_zero x).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨ξ, rfl⟩ := hy
    obtain ⟨η, rfl⟩ := hz
    exact ⟨ξ + η, (D.corr_add ξ η x).symm⟩
  | smul c y _ hy =>
    obtain ⟨ξ, rfl⟩ := hy
    exact ⟨c • ξ, (D.corr_smul c ξ x).symm⟩

/-- **Every class of the orbit span is a pole-plane class plus the action of a correspondence.** -/
theorem exists_eq_corr_of_mem_orbitSpan (x : E) {w : E} (hw : w ∈ D.orbitSpan x) :
    ∃ (a b : ℝ) (ξ : Correspondence G), w = D.corr ξ x + a • D.H + b • D.V := by
  rw [orbitSpan, Submodule.span_union, Submodule.mem_sup] at hw
  obtain ⟨u, hu, v, hv, rfl⟩ := hw
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨ξ, rfl⟩ := D.exists_corr_of_mem_span_orbit x hv
  exact ⟨a, b, ξ, by abel⟩

/-- **The defect is nonnegative on the orbit surface iff `x` is oriented.** -/
theorem orbitSurface_defect_nonneg_iff (x : E) :
    (∀ w : D.orbitSpan x, 0 ≤ (D.orbitSurface x).defect w w) ↔ D.OrbitHodgeIndex x := by
  rw [← D.rosatiPositive_iff_orbitHodgeIndex]
  constructor
  · intro h ξ
    have hmem : D.corr ξ x ∈ D.orbitSpan x :=
      Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (D.orbit_mem_orbitSpan x g)
    have := h ⟨_, hmem⟩
    rw [orbitSurface, PolarSurface.restrict_defect, D.defect_corr_corr] at this
    exact this
  · intro h w
    obtain ⟨a, b, ξ, hw⟩ := D.exists_eq_corr_of_mem_orbitSpan x w.2
    rw [orbitSurface, PolarSurface.restrict_defect, hw, D.defect_add_pole, D.defect_corr_corr]
    exact h ξ

/-- **Riemann–Roch on the orbit of a cycle is its orientation.** For every set `E` of classes of
the orbit surface of nonnegative ample degree satisfying the ample axiom, Riemann–Roch holds iff
`E` contains the open positive cone and `x` has the orbit Hodge index. -/
theorem orbitSurface_riemannRoch_iff (x : E) {E' : Set (D.orbitSpan x)}
    (hdeg : ∀ w ∈ E', 0 ≤ (D.orbitSurface x).pair w (D.orbitSurface x).ample)
    (hA : (D.orbitSurface x).AmpleAxiom E') :
    (D.orbitSurface x).RiemannRochAxiom E' ↔
      (D.orbitSurface x).openPositiveCone ⊆ E' ∧ D.OrbitHodgeIndex x := by
  rw [← D.orbitSurface_defect_nonneg_iff]
  exact (D.orbitSurface x).riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg hdeg hA

end ScalingDatum

/-! ### Instances: `ℤ` and configurations -/

theorem scalingAction_H (t : ℝ) :
    scalingAction t ((1, 0, 0) : ScalingCycle) = Real.exp (t / 2) • ((1, 0, 0) : ScalingCycle) := by
  ext <;> simp [scalingAction, scaleShift_zero_fun]

theorem scalingAction_V (t : ℝ) :
    scalingAction t ((0, 1, 0) : ScalingCycle) = Real.exp (-t / 2) • ((0, 1, 0) : ScalingCycle) := by
  ext <;> simp [scalingAction, scaleShift_zero_fun]

theorem zetaScalingDatum_fibreCompatible : zetaScalingDatum.FibreCompatible :=
  fun t => ⟨scalingAction_H t, scalingAction_V t⟩

theorem configScalingDatum_fibreCompatible (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    (configScalingDatum Z hZ).FibreCompatible :=
  fun t => ⟨scalingAction_H t, scalingAction_V t⟩

/-- **On a configuration, Riemann–Roch on the orbit surface is blindness to the off-line zeros.** -/
theorem configOrbitSurface_riemannRoch_iff_blind (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) (x : ScalingCycle) {E' : Set ((configScalingDatum Z hZ).orbitSpan x)}
    (hdeg : ∀ w ∈ E', 0 ≤ ((configScalingDatum Z hZ).orbitSurface x).pair w
      ((configScalingDatum Z hZ).orbitSurface x).ample)
    (hA : ((configScalingDatum Z hZ).orbitSurface x).AmpleAxiom E') :
    ((configScalingDatum Z hZ).orbitSurface x).RiemannRochAxiom E' ↔
      ((configScalingDatum Z hZ).orbitSurface x).openPositiveCone ⊆ E' ∧ BlindOffLine Z x.2.2 := by
  rw [(configScalingDatum Z hZ).orbitSurface_riemannRoch_iff x hdeg hA,
    (orientation_tfae Z hZ hFE x).out 1 2]

end GaloisForLFunctions.ArithmeticOrientationGeometry
