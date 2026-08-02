import GaloisForLFunctions.HTGeometry.RelativeContractionTransgressionLaw

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A0 A1 B0 B1 P : Type*}
variable [Field R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup B0] [Module R B0]
variable [AddCommGroup B1] [Module R B1]

def relativeAdmissionSpectrum
    (S : Submodule R A0) (d : A0 →ₗ[R] A1) (h : A1 →ₗ[R] A0)
    (x : P → A1) : Set P :=
  {p | relativePrimitiveObstruction S d h (x p) = 0}

theorem relativeAdmissionTransport_le_comap
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U) :
    S ⊔ LinearMap.ker d ≤ (U ⊔ LinearMap.ker e).comap T0 := by
  rw [sup_le_iff]
  constructor
  · intro a ha
    exact (show T0 a ∈ U ⊔ LinearMap.ker e from
      (le_sup_left : U ≤ U ⊔ LinearMap.ker e)
        (hsector (Submodule.mem_map_of_mem ha)))
  · intro a ha
    apply (le_sup_right : LinearMap.ker e ≤ U ⊔ LinearMap.ker e)
    change e (T0 a) = 0
    have h := LinearMap.congr_fun hchain a
    simp only [LinearMap.comp_apply] at h
    rw [h, show d a = 0 from ha, map_zero]

def relativeAdmissionQuotientMap
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U) :
    (A0 ⧸ (S ⊔ LinearMap.ker d)) →ₗ[R]
      (B0 ⧸ (U ⊔ LinearMap.ker e)) :=
  Submodule.mapQ (S ⊔ LinearMap.ker d) (U ⊔ LinearMap.ker e) T0
    (relativeAdmissionTransport_le_comap S U d e T0 T1 hchain hsector)

theorem relativeAdmissionSpectrum_mem_iff
    (S : Submodule R A0) (d : A0 →ₗ[R] A1) (h : A1 →ₗ[R] A0)
    (x : P → A1) (p : P) (hprimitive : d (h (x p)) = x p) :
    p ∈ relativeAdmissionSpectrum S d h x ↔
      ∃ b : A0, b ∈ S ∧ d b = x p := by
  exact relativePrimitiveObstruction_eq_zero_iff S d h (x p) hprimitive

theorem relativePrimitiveObstruction_eq_of_primitives
    (S : Submodule R A0) (d : A0 →ₗ[R] A1)
    (h h' : A1 →ₗ[R] A0) (x : A1)
    (hh : d (h x) = x) (hh' : d (h' x) = x) :
    relativePrimitiveObstruction S d h x =
      relativePrimitiveObstruction S d h' x := by
  apply (Submodule.Quotient.eq (S ⊔ LinearMap.ker d)).2
  apply (le_sup_right : LinearMap.ker d ≤ S ⊔ LinearMap.ker d)
  change d (h x - h' x) = 0
  rw [map_sub, hh, hh', sub_self]

theorem relativePrimitiveObstruction_natural
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : A1) (hsource : d (h x) = x)
    (htarget : e (k (T1 x)) = T1 x) :
    relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector
        (relativePrimitiveObstruction S d h x) =
      relativePrimitiveObstruction U e k (T1 x) := by
  apply (Submodule.Quotient.eq (U ⊔ LinearMap.ker e)).2
  apply (le_sup_right : LinearMap.ker e ≤ U ⊔ LinearMap.ker e)
  change e (T0 (h x) - k (T1 x)) = 0
  rw [map_sub, htarget]
  have hcomm := LinearMap.congr_fun hchain (h x)
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm, hsource, sub_self]

theorem relativeAdmissionSpectrum_natural_eq_of_injective
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : P → A1)
    (hsource : ∀ p, d (h (x p)) = x p)
    (htarget : ∀ p, e (k (T1 (x p))) = T1 (x p))
    (hinjective : Function.Injective
      (relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector)) :
    relativeAdmissionSpectrum S d h x =
      relativeAdmissionSpectrum U e k (fun p => T1 (x p)) := by
  ext p
  change relativePrimitiveObstruction S d h (x p) = 0 ↔
    relativePrimitiveObstruction U e k (T1 (x p)) = 0
  have hnat := relativePrimitiveObstruction_natural S U d e h k T0 T1
    hchain hsector (x p) (hsource p) (htarget p)
  constructor
  · intro hz
    rw [← hnat, hz, map_zero]
  · intro hz
    apply hinjective
    rw [hnat, hz, map_zero]

theorem relativeAdmissionTransport_information_loss
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : A1) (hsourcePrimitive : d (h x) = x)
    (htargetPrimitive : e (k (T1 x)) = T1 x)
    (hsource : relativePrimitiveObstruction S d h x ≠ 0)
    (htarget : relativePrimitiveObstruction U e k (T1 x) = 0) :
    ¬ Function.Injective
        (relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector) ∧
      relativePrimitiveObstruction S d h x ∈
        LinearMap.ker
          (relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector) := by
  have hnat := relativePrimitiveObstruction_natural S U d e h k T0 T1
    hchain hsector x hsourcePrimitive htargetPrimitive
  have hker :
      relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector
          (relativePrimitiveObstruction S d h x) = 0 := by
    rw [hnat, htarget]
  constructor
  · intro hinj
    apply hsource
    apply hinj
    rw [hker, map_zero]
  · exact hker

end

end GaloisForLFunctions.HTGeometry

