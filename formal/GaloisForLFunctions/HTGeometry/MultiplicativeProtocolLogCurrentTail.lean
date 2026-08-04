import GaloisForLFunctions.HTGeometry.MultiplicativeProtocolWitness
import GaloisForLFunctions.HTGeometry.ScalarInfiniteScaleFixedField
import GaloisForLFunctions.HTGeometry.ScalarFiniteDifferentialTorsor
import GaloisForLFunctions.HTGeometry.ScalarTailRationalTriviality

/-!
# The purely expanding multiplicative protocol keeps only the velocity

If the exponents of a multiplicative protocol accumulate without bound and the coefficient field
realizes each accumulated exponent by a primitive root of unity, then the phase tail of the protocol
is exactly the logarithmic-current field of the generator: every prefix image contains the current
`g'/g`, and an element of all of them carries infinitely many scaling symmetries, hence is a
rational function of the current alone.

This is the rank-one instance of the erasure dichotomy: the position coordinate is destroyed by the
protocol and the Maurer--Cartan velocity survives.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E] [CharZero C]

section

variable {g : E} (hg : DifferentialIndependent C (fun _ : Unit ↦ g))
  (hgen : differentialAdjoin C (Set.range fun _ : Unit ↦ g) = ⊤)

omit [Differential C] [DifferentialAlgebra C E] [CharZero E] [CharZero C] in
include hg in
theorem hypertranscendentalOver_gen : HypertranscendentalOver C g :=
  (hypertranscendentalOver_iff_differentialIndependent_singleton C g).mpr hg

omit [CharZero C] in
include hg hgen in
/-- The scaling automorphism of the protocol is the canonical scalar action of the rank-one
differential torsor: both are differential algebra automorphisms multiplying the generator by the
same constant. -/
theorem scaleEquiv_eq_scalarDifferentialScaleEquivCurrent
    (hconst : ∀ c : C, c′ = 0) (u : Cˣ) (z : E) :
    scaleEquiv hg hgen u z =
      scalarDifferentialScaleEquivCurrent g (hypertranscendentalOver_gen hg) (gen_ne_zero hg)
        (differentialAdjoin_singleton_eq_top hgen) hconst u z := by
  have heq : scaleEquiv hg hgen u
      = scalarDifferentialScaleEquiv g (hypertranscendentalOver_gen hg)
          (differentialAdjoin_singleton_eq_top hgen) u := by
    refine tailEquiv_ext (fun _ : Unit ↦ g) hgen (fun w ↦ scaleEquiv_deriv hg hgen u w)
      (fun w ↦ scalarDifferentialScaleEquiv_deriv g (hypertranscendentalOver_gen hg)
        (differentialAdjoin_singleton_eq_top hgen) u w) (fun _ ↦ ?_)
    rw [scaleEquiv_gen, scalarDifferentialScaleEquiv_apply_q, mul_comm]
  rw [heq]
  rfl

include hg hgen in
/-- **The purely expanding phase tail.**  With unbounded accumulated exponents, all realized by
primitive roots of unity, the tail of the multiplicative protocol is the logarithmic-current
field. -/
theorem multiplicativeProtocol_nonautonomousTail_eq_scalarLogCurrentField
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (i : ℕ) (hconst : ∀ c : C, c′ = 0)
    (hroot : ∀ n : ℕ, ∃ ζ : C, IsPrimitiveRoot ζ (prefixExponent m i n))
    (hunb : ∀ B : ℕ, ∃ n : ℕ, B < prefixExponent m i n) :
    nonautonomousTail (powerProtocol hg hgen m hm) i = scalarLogCurrentField C g := by
  classical
  have hg0 : g ≠ 0 := gen_ne_zero hg
  have hq : HypertranscendentalOver C g := hypertranscendentalOver_gen hg
  have htop : differentialAdjoin C ({g} : Set E) = ⊤ :=
    differentialAdjoin_singleton_eq_top hgen
  set S : Set Cˣ := {u : Cˣ | ∃ n : ℕ, u ^ prefixExponent m i n = 1} with hS
  have hSinf : S.Infinite := by
    intro hfin
    obtain ⟨n, hn⟩ := hunb S.ncard
    obtain ⟨ζ, hζ⟩ := hroot n
    have hsub : ((rootsOfUnity (prefixExponent m i n) C : Subgroup Cˣ) : Set Cˣ) ⊆ S := by
      intro u hu
      exact ⟨n, by simpa [mem_rootsOfUnity] using hu⟩
    have hle := Set.ncard_le_ncard hsub hfin
    haveI : NeZero (prefixExponent m i n) := ⟨(prefixExponent_pos hm i n).ne'⟩
    have hcard : ((rootsOfUnity (prefixExponent m i n) C : Subgroup Cˣ) : Set Cˣ).ncard
        = prefixExponent m i n := by
      show Nat.card _ = _
      simpa [Nat.card_eq_fintype_card] using hζ.card_rootsOfUnity
    omega
  refine le_antisymm ?_ ?_
  · intro z hz
    have hzmem : ∀ n : ℕ, z ∈ differentialAdjoin C ({g ^ prefixExponent m i n} : Set E) := by
      intro n
      have hz' : z ∈ ⨅ n : ℕ,
          IntermediateField.map (forwardPrefix (powerProtocol hg hgen m hm) i n) ⊤ := hz
      rw [← SetLike.mem_coe, IntermediateField.coe_iInf, Set.mem_iInter] at hz'
      have hzn := hz' n
      rw [SetLike.mem_coe, map_forwardPrefix_powerProtocol] at hzn
      exact hzn
    refine mem_scalarLogCurrentField_of_infinite_scale_fixed g hq hg0 htop hconst hSinf ?_
    rintro u ⟨n, hun⟩
    have hfixField := differentialAdjoin_pow_le_fixedField hg hgen
      (N := prefixExponent m i n) (hzmem n)
    rw [IntermediateField.mem_fixedField_iff] at hfixField
    have hmemroot : u ∈ rootsOfUnity (prefixExponent m i n) C := by
      simpa [mem_rootsOfUnity] using hun
    have hfix := hfixField (scaleRep hg hgen u) ⟨u, hmemroot, rfl⟩
    rw [scaleRep_eq, scaleEquiv_eq_scalarDifferentialScaleEquivCurrent hg hgen hconst u z] at hfix
    exact hfix
  · refine le_iInf fun n ↦ ?_
    rw [map_forwardPrefix_powerProtocol]
    exact scalarLogCurrentField_le_differentialAdjoin_pow g hg0 (prefixExponent_pos hm i n)


include hg hgen in
/-- **The surviving sector is one hypertranscendental coordinate.**  The tail of a purely expanding
multiplicative protocol is the differential field generated by the single hypertranscendental
element `g'/g`, and it contains no nonconstant rational function of `g`. -/
theorem multiplicativeProtocol_nonautonomousTail_velocity_only
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (i : ℕ) (hconst : ∀ c : C, c′ = 0)
    (hroot : ∀ n : ℕ, ∃ ζ : C, IsPrimitiveRoot ζ (prefixExponent m i n))
    (hunb : ∀ B : ℕ, ∃ n : ℕ, B < prefixExponent m i n) :
    nonautonomousTail (powerProtocol hg hgen m hm) i
        = differentialAdjoin C ({Differential.logDeriv g} : Set E) ∧
      HypertranscendentalOver C (Differential.logDeriv g) ∧
      nonautonomousTail (powerProtocol hg hgen m hm) i ⊓
        IntermediateField.adjoin C ({g} : Set E) = ⊥ := by
  have htail := multiplicativeProtocol_nonautonomousTail_eq_scalarLogCurrentField
    hg hgen m hm i hconst hroot hunb
  refine ⟨htail, logDeriv_hypertranscendentalOver (hypertranscendentalOver_gen hg)
    (gen_ne_zero hg), ?_⟩
  rw [htail]
  exact scalarLogCurrentField_inf_adjoin_eq_bot g (hypertranscendentalOver_gen hg) (gen_ne_zero hg)
    (differentialAdjoin_singleton_eq_top hgen) hconst

end

end

end GaloisForLFunctions.HTGeometry
