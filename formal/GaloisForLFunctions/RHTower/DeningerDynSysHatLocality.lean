import GaloisForLFunctions.RHTower.DeningerDynSysTiltLocalHom
import GaloisForLFunctions.RHTower.DeningerDynSysPerfectionUnique

/-!
# The locality clause of Deninger's Proposition 14.16

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.16
(`t1213n`), and the right square of Supplement 14.10 (`t106`).

The residue of a continuous pointed multiplicative map `P̂_y` on `lim_{()^p} Â` is prescribed on
the dense image of `lim_{()^p} A` by Deninger's `P̃_y`, hence on all of `lim_{()^p} Â` because
both sides are continuous into the discrete residue field.  Feeding an element whose zeroth
coefficient lies in the maximal ideal of `Â` gives `P̃_y (0) = 0`, so `P̂_y` maps the maximal ideal
of the tilt into the maximal ideal of `𝒪`, which is exactly the locality of `P̂_y^♭`.
-/

namespace RHTower

open Perfection

universe u

variable {p : ℕ} [Fact p.Prime]

/-- The residue map of a local ring is continuous for the discrete topology on the residue field
as soon as every coset of the maximal ideal is open. -/
theorem deningerContinuous_residue {R : Type u} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [TopologicalSpace (IsLocalRing.ResidueField R)]
    [DiscreteTopology (IsLocalRing.ResidueField R)]
    (h : ∀ a : R, IsOpen {b : R | b - a ∈ IsLocalRing.maximalIdeal R}) :
    Continuous (IsLocalRing.residue R) := by
  rw [continuous_def]
  intro U _
  have hcover : (IsLocalRing.residue R) ⁻¹' U
      = ⋃ a ∈ (IsLocalRing.residue R) ⁻¹' U,
          {b : R | b - a ∈ IsLocalRing.maximalIdeal R} := by
    ext b
    constructor
    · intro hb
      refine Set.mem_iUnion₂.2 ⟨b, hb, ?_⟩
      simp
    · intro hb
      obtain ⟨a, ha, hba⟩ := Set.mem_iUnion₂.1 hb
      have hres : IsLocalRing.residue R b = IsLocalRing.residue R a := by
        rw [← sub_eq_zero, ← map_sub]
        exact (IsLocalRing.residue_eq_zero_iff _).2 hba
      rw [Set.mem_preimage, hres]
      exact ha
  rw [hcover]
  exact isOpen_biUnion fun a _ => h a

/-- **Deninger, Proposition 14.16 (`t1213n`), the locality clause.**  If the residue of a
continuous pointed multiplicative map on `lim_{()^p} Â` is computed by `P̃_y` on the dense image of
`lim_{()^p} A`, then the associated homomorphism of tilts is a local homomorphism. -/
theorem deningerLimChar_isLocalHom_of_dense
    {A₀ A O : Type u} [CommRing A₀] [CommRing A] [CommRing O]
    [IsLocalRing A] [IsLocalRing O]
    [Fact (¬ IsUnit (p : A))] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : A)}) A] [IsAdicComplete (Ideal.span {(p : O)}) O]
    [TopologicalSpace A] [ContinuousMul A] [TopologicalSpace O]
    [TopologicalSpace (IsLocalRing.ResidueField A)] [DiscreteTopology (IsLocalRing.ResidueField A)]
    [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
    (hopenA : ∀ a : A, IsOpen {b : A | b - a ∈ IsLocalRing.maximalIdeal A})
    (hopenO : ∀ a : O, IsOpen {b : O | b - a ∈ IsLocalRing.maximalIdeal O})
    (φ : A₀ →+* A) (hφ : DenseRange φ) (hpow : ∀ a : A₀, ∃ b : A₀, b ^ p = a)
    (χflat : PreTilt A p →+* PreTilt O p)
    (hcont : Continuous (deningerLimChar χflat))
    (Ptilde : IsLocalRing.ResidueField A → IsLocalRing.ResidueField O) (hP : Ptilde 0 = 0)
    (hsq : ∀ f : Perfection A₀ p,
      IsLocalRing.residue O (deningerLimChar χflat (mapMonoidHom p φ.toMonoidHom f))
        = Ptilde (IsLocalRing.residue A
            (coeffMonoidHom A p 0 (mapMonoidHom p φ.toMonoidHom f)))) :
    IsLocalHom χflat := by
  have hF : Continuous fun z : Perfection A p =>
      IsLocalRing.residue O (deningerLimChar χflat z) :=
    (deningerContinuous_residue hopenO).comp hcont
  have hG : Continuous fun z : Perfection A p =>
      Ptilde (IsLocalRing.residue A (coeffMonoidHom A p 0 z)) :=
    continuous_of_discreteTopology.comp
      ((deningerContinuous_residue hopenA).comp
        (deningerPerfection_continuous_coeff (N := A) (p := p) 0))
  have heq := deningerPerfection_ext_of_dense hpow φ.toMonoidHom hφ hF hG hsq
  refine deningerLimChar_isLocalHom χflat fun z hz => ?_
  have h1 := congrFun heq z
  rw [(IsLocalRing.residue_eq_zero_iff _).2 hz, hP] at h1
  exact (IsLocalRing.residue_eq_zero_iff _).1 h1

end RHTower
