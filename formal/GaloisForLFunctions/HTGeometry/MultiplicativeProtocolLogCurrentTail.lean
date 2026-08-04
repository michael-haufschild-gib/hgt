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


omit [CharZero E] [CharZero C] in
/-- A power field of a divisor exponent contains the power field of the multiple. -/
theorem differentialAdjoin_pow_le_of_dvd (x : E) {d N : ℕ} (hdvd : d ∣ N) :
    differentialAdjoin C ({x ^ N} : Set E) ≤ differentialAdjoin C ({x ^ d} : Set E) := by
  obtain ⟨c, rfl⟩ := hdvd
  refine differentialAdjoin_le C ?_ (derivationClosed_differentialAdjoin C _)
  intro y hy
  have hyx : y = x ^ (d * c) := hy
  rw [hyx, pow_mul]
  exact pow_mem (subset_differentialAdjoin C ({x ^ d} : Set E) rfl) c

omit [CharZero C] in
include hg hgen in
/-- **The stabilizing phase tail.**  If the accumulated exponents are eventually constant, the tail
of the multiplicative protocol is the differential field of that stable power. -/
theorem multiplicativeProtocol_nonautonomousTail_eq_differentialAdjoin_pow
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (i : ℕ) {N k : ℕ}
    (hstab : ∀ n, k ≤ n → prefixExponent m i n = N) :
    nonautonomousTail (powerProtocol hg hgen m hm) i
      = differentialAdjoin C ({g ^ N} : Set E) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    have hz' : z ∈ ⨅ n : ℕ,
        IntermediateField.map (forwardPrefix (powerProtocol hg hgen m hm) i n) ⊤ := hz
    rw [← SetLike.mem_coe, IntermediateField.coe_iInf, Set.mem_iInter] at hz'
    have hzk := hz' k
    rw [SetLike.mem_coe, map_forwardPrefix_powerProtocol, hstab k le_rfl] at hzk
    exact hzk
  · refine le_iInf fun n ↦ ?_
    rw [map_forwardPrefix_powerProtocol]
    rcases Nat.lt_or_ge n k with hlt | hge
    · exact differentialAdjoin_pow_le_of_dvd g
        ((hstab k le_rfl) ▸ prefixExponent_dvd_of_le i (le_of_lt hlt))
    · rw [hstab n hge]

include hg hgen in
/-- **Position and velocity generate the phase tail.**  For every multiplicative protocol there is an
exponent `N` — the order of the reversible quotient, zero exactly when the position is completely
erased — with the tail generated by the position `g ^ N` and the velocity `g'/g`. -/
theorem multiplicativeProtocol_nonautonomousTail_position_velocity
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (i : ℕ) (hconst : ∀ c : C, c′ = 0)
    (hroot : ∀ n : ℕ, ∃ ζ : C, IsPrimitiveRoot ζ (prefixExponent m i n)) :
    ∃ N : ℕ, nonautonomousTail (powerProtocol hg hgen m hm) i
      = differentialAdjoin C ({g ^ N, Differential.logDeriv g} : Set E) := by
  have hg0 : g ≠ 0 := gen_ne_zero hg
  by_cases hbdd : ∃ B : ℕ, ∀ n, prefixExponent m i n ≤ B
  · obtain ⟨B, hB⟩ := hbdd
    obtain ⟨N, k, hNpos, hstab⟩ := exists_stable_prefixExponent hm i hB
    refine ⟨N, ?_⟩
    rw [multiplicativeProtocol_nonautonomousTail_eq_differentialAdjoin_pow hg hgen m hm i hstab]
    refine le_antisymm ?_ ?_
    · refine differentialAdjoin_le C ?_ (derivationClosed_differentialAdjoin C _)
      intro y hy
      have hyx : y = g ^ N := hy
      rw [hyx]
      exact subset_differentialAdjoin C _ (Set.mem_insert _ _)
    · refine differentialAdjoin_le C ?_ (derivationClosed_differentialAdjoin C _)
      intro y hy
      rcases hy with hy | hy
      · rw [hy]
        exact subset_differentialAdjoin C _ rfl
      · have hyJ : y = Differential.logDeriv g := hy
        rw [hyJ]
        exact scalarLogCurrentField_le_differentialAdjoin_pow g hg0 hNpos
          (subset_differentialAdjoin C _ rfl)
  · push Not at hbdd
    have hunb : ∀ B : ℕ, ∃ n : ℕ, B < prefixExponent m i n := by
      intro B
      obtain ⟨n, hn⟩ := hbdd B
      exact ⟨n, hn⟩
    refine ⟨0, ?_⟩
    rw [multiplicativeProtocol_nonautonomousTail_eq_scalarLogCurrentField
      hg hgen m hm i hconst hroot hunb]
    refine le_antisymm ?_ ?_
    · refine differentialAdjoin_le C ?_ (derivationClosed_differentialAdjoin C _)
      intro y hy
      have hyJ : y = Differential.logDeriv g := hy
      rw [hyJ]
      exact subset_differentialAdjoin C _ (Set.mem_insert_of_mem _ rfl)
    · refine differentialAdjoin_le C ?_ (derivationClosed_differentialAdjoin C _)
      intro y hy
      rcases hy with hy | hy
      · rw [hy, pow_zero]
        exact one_mem _
      · have hyJ : y = Differential.logDeriv g := hy
        rw [hyJ]
        exact subset_differentialAdjoin C _ rfl

omit [CharZero C] in
include hg hgen in
/-- **Flat velocity transport.**  A protocol step multiplies the velocity by its exponent, and that
multiplication is a bijection of the velocity line. -/
theorem logDeriv_powerEndo (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (j : ℕ) :
    Differential.logDeriv (powerProtocol hg hgen m hm j g)
        = (m j : E) * Differential.logDeriv g ∧
      Function.Bijective (fun z : E ↦ (m j : E) * z) := by
  have hg0 : g ≠ 0 := gen_ne_zero hg
  have hmne : (m j : E) ≠ 0 := Nat.cast_ne_zero.mpr (hm j).ne'
  refine ⟨?_, ⟨fun x y hxy ↦ by field_simp at hxy; exact hxy,
    fun y ↦ ⟨y / (m j : E), by field_simp⟩⟩⟩
  change Differential.logDeriv (powerEndo hg hgen (hm j) g) = _
  rw [powerEndo_gen, differential_logDeriv_pow g hg0]

end

end

end GaloisForLFunctions.HTGeometry
