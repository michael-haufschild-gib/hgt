import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGeneralizedZeroJetDescent

/-!
# Paugam spectral pairing on actual Meyer cohomology

For a generalized zeta-zero jet `Eρ`, this file constructs the intrinsic
Paugam form

`ψρ(u,v) = Eρ(u) Eρ(Jv) - Eρ(v) Eρ(Ju)`

directly on the genuine all-weight Meyer quotient.  Boundary descent is not
postulated: it follows from the differentiated Poisson--Mellin factorization.
The form is alternating, is anti-invariant under simultaneous weighted
reciprocal inversion, and becomes the signed determinant of the `ρ` and
`1 - ρ` jets.

The radical audit is exact.  A single spectral pair cannot be declared
globally nondegenerate: when one nonzero determinant witness exists, its
radical is precisely the simultaneous kernel of the two reflected
coordinates.  Eliminating that remaining common kernel requires the global
nuclear spectral completeness theorem; it is not hidden behind a positivity
or semisimplicity assumption here.

All Lean statements are unconditional.  No RH, trace formula, numerical
computation, or spectral-realization axiom occurs.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Classical

namespace RHTower

noncomputable section

/-- A spectral point together with enough zeta vanishing to support one generalized jet. -/
structure DeningerMeyerZetaZeroJetDatum where
  point : ℂ
  re_pos : 0 < point.re
  ne_one : point ≠ 1
  jetOrder : ℕ
  zeta_vanishing :
    ∀ j ≤ jetOrder,
      iteratedDeriv j riemannZeta point = 0

/-- Generalized zero-jet evaluation on actual Meyer cohomology. -/
def DeningerMeyerZetaZeroJetDatum.evaluationLM
    (d : DeningerMeyerZetaZeroJetDatum) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  deningerMeyerZetaZeroJetEvaluationLM
    d.point d.re_pos d.ne_one d.jetOrder d.zeta_vanishing

/-- The reflected evaluation `u ↦ Eρ(Ju)`. -/
def DeningerMeyerZetaZeroJetDatum.reflectedEvaluationLM
    (d : DeningerMeyerZetaZeroJetDatum) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  d.evaluationLM.comp deningerMeyerStrongLogCohomologyJ

/--
The single generalized-zero Paugam form
`Eρ(u) Eρ(Jv) - Eρ(v) Eρ(Ju)`.
-/
def deningerMeyerPaugamZeroJetPairing
    (d : DeningerMeyerZetaZeroJetDatum) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := fun v =>
        d.evaluationLM u * d.reflectedEvaluationLM v -
          d.evaluationLM v * d.reflectedEvaluationLM u
      map_add' := by
        intro v w
        simp only [
          LinearMap.map_add,
          mul_add, add_mul]
        ring
      map_smul' := by
        intro c v
        simp only [
          LinearMap.map_smul,
          RingHom.id_apply,
          smul_eq_mul]
        ring }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    simp only [
      LinearMap.add_apply,
      LinearMap.coe_mk,
      AddHom.coe_mk,
      LinearMap.map_add,
      add_mul, mul_add]
    ring
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    simp only [
      LinearMap.smul_apply,
      LinearMap.coe_mk,
      AddHom.coe_mk,
      LinearMap.map_smul,
      RingHom.id_apply,
      smul_eq_mul]
    ring

theorem deningerMeyerPaugamZeroJetPairing_apply
    (d : DeningerMeyerZetaZeroJetDatum)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamZeroJetPairing d u v =
      d.evaluationLM u * d.reflectedEvaluationLM v -
        d.evaluationLM v * d.reflectedEvaluationLM u :=
  rfl

@[simp]
theorem deningerMeyerPaugamZeroJetPairing_self
    (d : DeningerMeyerZetaZeroJetDatum)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamZeroJetPairing d u u = 0 := by
  rw [deningerMeyerPaugamZeroJetPairing_apply]
  ring

theorem deningerMeyerPaugamZeroJetPairing_skew
    (d : DeningerMeyerZetaZeroJetDatum)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamZeroJetPairing d u v =
      -deningerMeyerPaugamZeroJetPairing d v u := by
  rw [deningerMeyerPaugamZeroJetPairing_apply,
    deningerMeyerPaugamZeroJetPairing_apply]
  ring

/-- Simultaneous weighted reciprocal inversion reverses the Paugam form. -/
theorem deningerMeyerPaugamZeroJetPairing_J
    (d : DeningerMeyerZetaZeroJetDatum)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamZeroJetPairing d
        (deningerMeyerStrongLogCohomologyJ u)
        (deningerMeyerStrongLogCohomologyJ v) =
      -deningerMeyerPaugamZeroJetPairing d u v := by
  rw [deningerMeyerPaugamZeroJetPairing_apply,
    deningerMeyerPaugamZeroJetPairing_apply]
  simp only [
    DeningerMeyerZetaZeroJetDatum.reflectedEvaluationLM,
    LinearMap.comp_apply,
    deningerMeyerStrongLogCohomologyJ_sq]
  ring

/--
For a reflected zero of the same jet order, the intrinsic `Eρ ∘ J` form is
the signed determinant of the `ρ` and `1 - ρ` generalized evaluations.
-/
theorem deningerMeyerPaugamZeroJetPairing_eq_reflectedDet
    (d : DeningerMeyerZetaZeroJetDatum)
    (hσ0 : 0 < (1 - d.point).re)
    (hσ1 : 1 - d.point ≠ 1)
    (hζreflected :
      ∀ j ≤ d.jetOrder,
        iteratedDeriv j riemannZeta (1 - d.point) = 0)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamZeroJetPairing d u v =
      (-1 : ℂ) ^ d.jetOrder *
        (d.evaluationLM u *
            deningerMeyerZetaZeroJetEvaluationLM
              (1 - d.point) hσ0 hσ1 d.jetOrder
              hζreflected v -
          d.evaluationLM v *
            deningerMeyerZetaZeroJetEvaluationLM
              (1 - d.point) hσ0 hσ1 d.jetOrder
              hζreflected u) := by
  rw [deningerMeyerPaugamZeroJetPairing_apply]
  change
    d.evaluationLM u *
          deningerMeyerZetaZeroJetEvaluationLM
            d.point d.re_pos d.ne_one d.jetOrder
            d.zeta_vanishing
            (deningerMeyerStrongLogCohomologyJ v) -
        d.evaluationLM v *
          deningerMeyerZetaZeroJetEvaluationLM
            d.point d.re_pos d.ne_one d.jetOrder
            d.zeta_vanishing
            (deningerMeyerStrongLogCohomologyJ u) =
      _
  rw [
    deningerMeyerZetaZeroJetEvaluationLM_J
      d.point d.re_pos d.ne_one hσ0 hσ1
        d.jetOrder d.zeta_vanishing hζreflected v,
    deningerMeyerZetaZeroJetEvaluationLM_J
      d.point d.re_pos d.ne_one hσ0 hσ1
        d.jetOrder d.zeta_vanishing hζreflected u]
  ring

/--
The simultaneous kernel of a jet and its reflected jet is always contained
in the radical of the associated Paugam form.
-/
theorem deningerMeyerPaugamZeroJet_commonKernel_le_radical
    (d : DeningerMeyerZetaZeroJetDatum) :
    LinearMap.ker d.evaluationLM ⊓
        LinearMap.ker d.reflectedEvaluationLM ≤
      LinearMap.ker (deningerMeyerPaugamZeroJetPairing d) := by
  intro u hu
  rw [Submodule.mem_inf] at hu
  rw [LinearMap.mem_ker] at hu
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  intro v
  rw [deningerMeyerPaugamZeroJetPairing_apply,
    hu.1, hu.2]
  simp

/--
If one pair of quotient classes has nonzero determinant, the Paugam radical
is exactly the simultaneous kernel of the zero jet and its reflected jet.
-/
theorem deningerMeyerPaugamZeroJet_radical_eq_commonKernel
    (d : DeningerMeyerZetaZeroJetDatum)
    {p q : DeningerMeyerStrongLogCohomology}
    (hpq : deningerMeyerPaugamZeroJetPairing d p q ≠ 0) :
    LinearMap.ker (deningerMeyerPaugamZeroJetPairing d) =
      LinearMap.ker d.evaluationLM ⊓
        LinearMap.ker d.reflectedEvaluationLM := by
  apply le_antisymm
  · intro u hu
    rw [LinearMap.mem_ker] at hu
    have hup :
        deningerMeyerPaugamZeroJetPairing d u p = 0 := by
      exact LinearMap.congr_fun hu p
    have huq :
        deningerMeyerPaugamZeroJetPairing d u q = 0 := by
      exact LinearMap.congr_fun hu q
    have hEval :
        d.evaluationLM u *
          deningerMeyerPaugamZeroJetPairing d p q = 0 := by
      rw [deningerMeyerPaugamZeroJetPairing_apply] at hup huq ⊢
      calc
        d.evaluationLM u *
            (d.evaluationLM p * d.reflectedEvaluationLM q -
              d.evaluationLM q * d.reflectedEvaluationLM p) =
          d.evaluationLM p *
              (d.evaluationLM u * d.reflectedEvaluationLM q -
                d.evaluationLM q * d.reflectedEvaluationLM u) -
            d.evaluationLM q *
              (d.evaluationLM u * d.reflectedEvaluationLM p -
                d.evaluationLM p * d.reflectedEvaluationLM u) := by
            ring
        _ = 0 := by rw [hup, huq]; ring
    have hReflected :
        d.reflectedEvaluationLM u *
          deningerMeyerPaugamZeroJetPairing d p q = 0 := by
      rw [deningerMeyerPaugamZeroJetPairing_apply] at hup huq ⊢
      calc
        d.reflectedEvaluationLM u *
            (d.evaluationLM p * d.reflectedEvaluationLM q -
              d.evaluationLM q * d.reflectedEvaluationLM p) =
          d.reflectedEvaluationLM p *
              (d.evaluationLM u * d.reflectedEvaluationLM q -
                d.evaluationLM q * d.reflectedEvaluationLM u) -
            d.reflectedEvaluationLM q *
              (d.evaluationLM u * d.reflectedEvaluationLM p -
                d.evaluationLM p * d.reflectedEvaluationLM u) := by
            ring
        _ = 0 := by rw [hup, huq]; ring
    rw [Submodule.mem_inf]
    constructor
    · rw [LinearMap.mem_ker]
      exact (mul_eq_zero.mp hEval).resolve_right hpq
    · rw [LinearMap.mem_ker]
      exact (mul_eq_zero.mp hReflected).resolve_right hpq
  · exact deningerMeyerPaugamZeroJet_commonKernel_le_radical d

end

end RHTower
