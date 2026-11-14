import GaloisForLFunctions.RepresentationLifting.CyclicSelfExtension
import GaloisForLFunctions.RepresentationLifting.CyclicRegularCoordinates

/-!
# Splitting and trace on the additive axis

Restrict the cyclic self-extension to the additive coefficient group. A contraction
of its acyclic differential gives an equivariant retraction. For every retraction
`r`, the composite `rΦ` commutes with `d` and agrees with the even projection on
`im d`. The norm is rank one, so the contraction trace formula gives `tr(rΦ) = 2`.

This proves the distinguished-line assertion of Scavia's Lemma 6.3 over every
field and every finite cyclic group, including characteristic two.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.RepresentationLifting
universe u
variable (k G : Type u) [Field k] [CommGroup G] [Fintype G] [IsCyclic G]

/-- An endomorphism commuting with `d` and acting as the even projection on boundaries has trace two. -/
theorem cyclicDifferential_trace_of_boundary_action
    (T : Module.End k (CyclicDetector k G))
    (hcomm : T * cyclicDifferential k G = cyclicDifferential k G * T)
    (hboundary : T * cyclicDifferential k G = cyclicEven k G * cyclicDifferential k G) :
    LinearMap.trace k (CyclicDetector k G) T = 2 := by
  let w : CyclicDetector k G := (cyclicNormVector k G, 0)
  let f : CyclicDetector k G →ₗ[k] k :=
    (cyclicAugmentation k G).comp (LinearMap.snd k _ _)
  have hd : cyclicEven k G * cyclicDifferential k G = f.smulRight w := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · exact cyclicRegularNorm_eq_smul k G v.2
    · change (0 : CyclicRegular k G) = f v • 0
      rw [smul_zero]
  have hu : cyclicDifferential k G (0, MonoidAlgebra.single 1 1) = w := by
    apply Prod.ext
    · change cyclicRegularNorm k G (MonoidAlgebra.single 1 1) = cyclicNormVector k G
      rw [cyclicRegularNorm_eq_smul, cyclicAugmentation_single, one_smul]
    · exact map_zero _
  have hw : cyclicDifferential k G w = 0 := by
    rw [← hu]
    exact cyclicDifferential_sq k G _
  obtain ⟨s, hs, htrace⟩ :=
    acyclic_squareZero_trace_formula (cyclicDifferential k G) (cyclicDifferential_exact k G)
  have hds : cyclicDifferential k G (s w) = w := by
    have h := LinearMap.congr_fun hs w
    change cyclicDifferential k G (s w) + s (cyclicDifferential k G w) = w at h
    simpa only [hw, map_zero, add_zero] using h
  have hf : f (s w) = 1 := by
    have h := congrArg (fun v : CyclicDetector k G =>
      (v.1 : MonoidAlgebra k G).coeff 1) hds
    change (cyclicRegularNorm k G (s w).2).coeff 1 = (cyclicNormVector k G).coeff 1 at h
    rw [cyclicRegularNorm_eq_smul, cyclicNormVector_coeff] at h
    change ((f (s w) • cyclicNormVector k G) : MonoidAlgebra k G).coeff 1 = 1 at h
    rw [MonoidAlgebra.coeff_smul] at h
    simpa only [Finsupp.smul_apply, smul_eq_mul, cyclicNormVector_coeff, mul_one] using h
  have hsdT : s * cyclicDifferential k G * T = s * cyclicEven k G * cyclicDifferential k G := by
    rw [mul_assoc, ← hcomm, hboundary, ← mul_assoc]
  have hscomp : s * cyclicEven k G * cyclicDifferential k G = f.smulRight (s w) := by
    rw [mul_assoc, hd]
    apply LinearMap.ext
    intro v
    exact map_smul s (f v) w
  rw [htrace T hcomm, hsdT, hscomp, LinearMap.trace_smulRight, hf, mul_one]

/-- A contraction and the grading sign give the linear retraction on the extension. -/
def cyclicInfinityRetractionLinear (s : Module.End k (CyclicDetector k G)) :
    CyclicExtensionSpace k G →ₗ[k] CyclicDetector k G :=
  s.comp ((cyclicSign k G).comp (LinearMap.fst k _ _)) +
    (cyclicDifferential k G).comp (s.comp ((cyclicSign k G).comp (LinearMap.snd k _ _)))

/-- The retraction commutes with every scalar multiple of the square-zero action. -/
def cyclicInfinityRetraction (s : Module.End k (CyclicDetector k G)) :
    Rep.res (MonoidHom.inr G (Multiplicative k)) (Rep.of (cyclicExtensionRepresentation k G)) ⟶
      Rep.res (MonoidHom.inr G (Multiplicative k)) (Rep.of (cyclicProductRepresentation k G)) :=
  Rep.ofHom ⟨cyclicInfinityRetractionLinear k G s, fun a => by
    apply LinearMap.ext
    intro p
    change cyclicInfinityRetractionLinear k G s
        (cyclicExtensionRepresentation k G (1, Multiplicative.ofAdd a.toAdd) p) =
      cyclicProductRepresentation k G (1, Multiplicative.ofAdd a.toAdd)
        (cyclicInfinityRetractionLinear k G s p)
    rw [cyclicExtensionRepresentation_unipotent, cyclicProductRepresentation_unipotent]
    change s (cyclicSign k G p.1) +
        cyclicDifferential k G (s (cyclicSign k G (p.2 + a.toAdd • p.1))) =
      (s (cyclicSign k G p.1) + cyclicDifferential k G (s (cyclicSign k G p.2))) +
        a.toAdd • cyclicDifferential k G
          (s (cyclicSign k G p.1) + cyclicDifferential k G (s (cyclicSign k G p.2)))
    simp only [map_add, map_smul, cyclicDifferential_sq, add_zero]
    abel⟩

/-- The contraction identity makes this equivariant map a left inverse of the inclusion. -/
theorem cyclicInfinityRetraction_inclusion (s : Module.End k (CyclicDetector k G))
    (hs : cyclicDifferential k G * s + s * cyclicDifferential k G = 1) :
    (Rep.resFunctor (MonoidHom.inr G (Multiplicative k))).map (cyclicSelfExtensionInclusion k G) ≫
      cyclicInfinityRetraction k G s = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change s (cyclicSign k G (-cyclicDifferential k G (cyclicSign k G v))) +
    cyclicDifferential k G (s (cyclicSign k G (cyclicSign k G v))) = v
  rw [map_neg, cyclicSign_anticommutes, cyclicSign_sq, neg_neg, add_comm]
  exact LinearMap.congr_fun hs v

/-- The cyclic self-extension splits after restriction to the additive coefficient group. -/
theorem cyclicSelfExtension_infinity_splits :
    ∃ r : Rep.res (MonoidHom.inr G (Multiplicative k)) (Rep.of (cyclicExtensionRepresentation k G)) ⟶
        Rep.res (MonoidHom.inr G (Multiplicative k)) (Rep.of (cyclicProductRepresentation k G)),
      (Rep.resFunctor (MonoidHom.inr G (Multiplicative k))).map
        (cyclicSelfExtensionInclusion k G) ≫ r = 𝟙 _ := by
  obtain ⟨s, hs⟩ := acyclic_squareZero_contracting (cyclicDifferential k G) (cyclicDifferential_exact k G)
  exact ⟨cyclicInfinityRetraction k G s, cyclicInfinityRetraction_inclusion k G s hs⟩

/-- On boundaries, the lift is the inclusion composed with the even projection. -/
theorem cyclicExtensionLift_boundary (v : CyclicDetector k G) :
    cyclicExtensionLift k G (cyclicDifferential k G v) =
      cyclicExtensionInclusion k G (cyclicEven k G (cyclicDifferential k G v)) := by
  have hdh : cyclicDifferential k G (cyclicEven k G (cyclicDifferential k G v)) = 0 := by
    apply Prod.ext
    · exact map_zero _
    · have h := congrArg (fun z : CyclicDetector k G => z.2) (cyclicDifferential_sq k G v)
      exact h
  have hS : cyclicSign k G (cyclicEven k G (cyclicDifferential k G v)) =
      cyclicEven k G (cyclicDifferential k G v) := by
    simp [cyclicSign, cyclicEven]
  rw [cyclicExtensionLift_d]
  change (0, cyclicEven k G (cyclicDifferential k G v)) =
    (-cyclicDifferential k G (cyclicSign k G (cyclicEven k G (cyclicDifferential k G v))),
      cyclicSign k G (cyclicEven k G (cyclicDifferential k G v)))
  rw [hS, hdh, neg_zero]

/-- Every additive-axis retraction gives the same trace, namely two. -/
theorem cyclicSelfExtension_infinity_trace
    (r : Rep.res (MonoidHom.inr G (Multiplicative k)) (Rep.of (cyclicExtensionRepresentation k G)) ⟶
      Rep.res (MonoidHom.inr G (Multiplicative k)) (Rep.of (cyclicProductRepresentation k G)))
    (hr : (Rep.resFunctor (MonoidHom.inr G (Multiplicative k))).map
      (cyclicSelfExtensionInclusion k G) ≫ r = 𝟙 _) :
    LinearMap.trace k (CyclicDetector k G)
      (((Rep.resFunctor (MonoidHom.inr G (Multiplicative k))).map
        (cyclicSelfExtensionLift k G) ≫ r).hom.toLinearMap) = 2 := by
  let T := (Rep.resFunctor (MonoidHom.inr G (Multiplicative k))).map
    (cyclicSelfExtensionLift k G) ≫ r
  apply cyclicDifferential_trace_of_boundary_action k G T.hom.toLinearMap
  · apply LinearMap.ext
    intro v
    change T.hom (cyclicDifferential k G v) = cyclicDifferential k G (T.hom v)
    have h := Rep.hom_comm_apply T (Multiplicative.ofAdd (1 : k)) v
    change T.hom (cyclicProductRepresentation k G (1, Multiplicative.ofAdd (1 : k)) v) =
      cyclicProductRepresentation k G (1, Multiplicative.ofAdd (1 : k)) (T.hom v) at h
    simpa only [cyclicProductRepresentation_unipotent, one_smul, map_add, add_right_inj] using h
  · apply LinearMap.ext
    intro v
    change r.hom (cyclicExtensionLift k G (cyclicDifferential k G v)) =
      cyclicEven k G (cyclicDifferential k G v)
    rw [cyclicExtensionLift_boundary]
    exact LinearMap.congr_fun (congrArg (fun f => f.hom.toLinearMap) hr) _

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicSelfExtension_infinity_splits
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicSelfExtension_infinity_trace
