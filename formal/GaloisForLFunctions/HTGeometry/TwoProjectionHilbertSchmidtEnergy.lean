/-
# Hilbert--Schmidt energy splitting for two quantum projections

The supersymmetric calculus of two projections separates a zero-mode-corrected complement into
two orthogonal transition channels.  If

`C = Z - (1 - P - R)`

and

`D = (1 - R)(1 - P) - Z`,

then `C = RP - D`.  For orthogonal projections the two summands are Hilbert--Schmidt orthogonal:
the range of `RP` lies in the `R` sector, whereas the range of `D` lies in the complementary
sector after removal of the joint zero mode.  Consequently

`||C||_HS^2 = ||RP||_HS^2 + ||D||_HS^2`.

This is the trace-energy form of the two-projection supersymmetry used for pairs of Fermi
projections.  It is a static value relation and needs no spectral decomposition.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry

noncomputable section

namespace HTGeometry

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The overlap of the complementary projection sectors after subtracting the specified joint
zero-mode projection. -/
def twoProjectionExteriorOverlap
    (P R Z : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 - R) * (1 - P) - Z

/-- The positive compression of `R` to the `P` sector.  In time--frequency language this is
the prolate/localization block; in the supersymmetric pairing it is the interior Hamiltonian. -/
def twoProjectionInteriorCompression
    (P R : H →L[ℂ] H) : H →L[ℂ] H :=
  P * R * P

/-- The transition from the `P` sector to its orthogonal complement through `R`.  This is the
off-diagonal supercharge channel and the free-fermion number-fluctuation corner. -/
def twoProjectionTransition
    (P R : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 - P) * R * P

/-- The common-zero-mode-subtracted compression of the complementary `R` sector to the
complementary `P` sector.  This is the exterior positive Hamiltonian paired with
`twoProjectionInteriorCompression`. -/
def twoProjectionExteriorCompression
    (P R Z : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 - P) * (1 - R) * (1 - P) - Z

private theorem hsInner_eq_zero_of_adjoint_comp_eq_zero
    (S T : H →L[ℂ] H)
    (hzero : ContinuousLinearMap.adjoint S ∘L T = 0) :
    hsInner S T = 0 := by
  have htrace :
      opTrace (ContinuousLinearMap.adjoint S ∘L T) = hsInner S T := by
    simpa using opTrace_comp_eq_hsInner (ContinuousLinearMap.adjoint S) T
  calc
    hsInner S T = opTrace (ContinuousLinearMap.adjoint S ∘L T) := htrace.symm
    _ = opTrace 0 := congrArg opTrace hzero
    _ = 0 := by simp [opTrace]

private theorem adjoint_sub_twoProjectionEnergy
    (S T : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (S - T) =
      ContinuousLinearMap.adjoint S - ContinuousLinearMap.adjoint T := by
  let adj : (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] (H →L[ℂ] H) :=
    ContinuousLinearMap.adjoint
  exact adj.map_sub S T

private theorem adjoint_one_sub_twoProjectionEnergy
    (P : H →L[ℂ] H) (hPadj : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (1 - P) = 1 - P := by
  rw [ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one, hPadj]

private theorem isHilbertSchmidt_pow_succ
    (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T) (n : ℕ) :
    IsHilbertSchmidt (T ^ (n + 1)) := by
  simpa only [ContinuousLinearMap.mul_def, pow_succ] using hT.comp_left (T ^ n)

private theorem summable_inner_diag_pow_add_two
    (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T) (n : ℕ) :
    Summable (fun i => inner ℂ (hsBasis ℂ H i) ((T ^ (n + 2)) (hsBasis ℂ H i))) := by
  have hPow := isHilbertSchmidt_pow_succ T hT n
  have hEq : T ^ (n + 2) = (T ^ (n + 1)) ∘L T := by
    change T ^ (n + 2) = T ^ (n + 1) * T
    simpa only [Nat.add_assoc] using pow_succ T (n + 1)
  rw [hEq]
  exact summable_inner_diag_comp hPow hT (hsBasis ℂ H)

private theorem opTrace_sub_eq_sub_of_summable_diag
    (S T : H →L[ℂ] H)
    (hS : Summable (fun i => inner ℂ (hsBasis ℂ H i) (S (hsBasis ℂ H i))))
    (hT : Summable (fun i => inner ℂ (hsBasis ℂ H i) (T (hsBasis ℂ H i)))) :
    opTrace (S - T) = opTrace S - opTrace T := by
  unfold opTrace
  calc
    ∑' i, inner ℂ (hsBasis ℂ H i) ((S - T) (hsBasis ℂ H i)) =
        ∑' i, (inner ℂ (hsBasis ℂ H i) (S (hsBasis ℂ H i)) -
          inner ℂ (hsBasis ℂ H i) (T (hsBasis ℂ H i))) := by
      exact tsum_congr fun i => by rw [sub_apply, inner_sub_right]
    _ = (∑' i, inner ℂ (hsBasis ℂ H i) (S (hsBasis ℂ H i))) -
          ∑' i, inner ℂ (hsBasis ℂ H i) (T (hsBasis ℂ H i)) :=
      hS.tsum_sub hT

/-- Operator trace is linear on the difference of two powers of a Hilbert--Schmidt operator from
degree two onward; both powers have explicit Hilbert--Schmidt product factorizations. -/
theorem opTrace_pow_add_two_sub_pow_add_three_of_isHilbertSchmidt
    (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T) (n : ℕ) :
    opTrace (T ^ (n + 2) - T ^ (n + 3)) =
      opTrace (T ^ (n + 2)) - opTrace (T ^ (n + 3)) :=
  opTrace_sub_eq_sub_of_summable_diag _ _
    (summable_inner_diag_pow_add_two T hT n)
    ((summable_inner_diag_pow_add_two T hT (n + 1)).congr fun i => by
      simp only [Nat.add_assoc])

/-- The overlap splits into its `P`-sector compression and its off-diagonal transition. -/
theorem twoProjection_overlap_eq_interiorCompression_add_transition
    (P R : H →L[ℂ] H) :
    R * P = twoProjectionInteriorCompression P R + twoProjectionTransition P R := by
  rw [twoProjectionInteriorCompression, twoProjectionTransition]
  noncomm_ring

/-- For self-adjoint `P,R`, the reverse transition is the adjoint of the forward transition. -/
theorem adjoint_twoProjectionTransition
    (P R : H →L[ℂ] H)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R) :
    ContinuousLinearMap.adjoint (twoProjectionTransition P R) =
      P * R * (1 - P) := by
  rw [twoProjectionTransition]
  change ContinuousLinearMap.adjoint (((1 - P) ∘L R) ∘L P) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    hPadj, hRadj, adjoint_one_sub_twoProjectionEnergy P hPadj] <;>
    ext x <;> rfl

/-- The interior compression is self-adjoint when both projections are. -/
theorem adjoint_twoProjectionInteriorCompression
    (P R : H →L[ℂ] H)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R) :
    ContinuousLinearMap.adjoint (twoProjectionInteriorCompression P R) =
      twoProjectionInteriorCompression P R := by
  rw [twoProjectionInteriorCompression]
  change ContinuousLinearMap.adjoint ((P ∘L R) ∘L P) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    hPadj, hRadj] <;> ext x <;> rfl

/-- **Two-projection Shannon trace law.**  The trace of the positive compression `PRP` is
exactly the Hilbert--Schmidt energy of the overlap `RP`.  Thus a time--band overlap area can be
used directly as the trace (effective dimension) of its localization operator, with no spectral
decomposition. -/
theorem re_opTrace_twoProjectionInteriorCompression_eq_hsNormSq_overlap
    (P R : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hRP : IsHilbertSchmidt (R * P)) :
    Complex.re (opTrace (twoProjectionInteriorCompression P R)) =
      hsNormSq (R * P) := by
  have hAdj : ContinuousLinearMap.adjoint (R * P) = P * R := by
    change ContinuousLinearMap.adjoint (R ∘L P) = P ∘L R
    rw [ContinuousLinearMap.adjoint_comp, hPadj, hRadj]
  have hEnergy :
      ContinuousLinearMap.adjoint (R * P) ∘L (R * P) =
        twoProjectionInteriorCompression P R := by
    rw [hAdj, twoProjectionInteriorCompression]
    have hRR : R * R = R := hR
    change (P * R) * (R * P) = P * R * P
    calc
      (P * R) * (R * P) = P * (R * R) * P := by simp only [mul_assoc]
      _ = P * R * P := by rw [hRR]
  calc
    Complex.re (opTrace (twoProjectionInteriorCompression P R)) =
        Complex.re
          (opTrace (ContinuousLinearMap.adjoint (R * P) ∘L (R * P))) := by
      rw [hEnergy]
    _ = hsNormSq (R * P) := re_opTrace_adjoint_comp_self hRP

/-- The zero-mode-subtracted exterior compression is self-adjoint. -/
theorem adjoint_twoProjectionExteriorCompression
    (P R Z : H →L[ℂ] H)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hZadj : ContinuousLinearMap.adjoint Z = Z) :
    ContinuousLinearMap.adjoint (twoProjectionExteriorCompression P R Z) =
      twoProjectionExteriorCompression P R Z := by
  rw [twoProjectionExteriorCompression, adjoint_sub_twoProjectionEnergy]
  change ContinuousLinearMap.adjoint (((1 - P) ∘L (1 - R)) ∘L (1 - P)) -
      ContinuousLinearMap.adjoint Z = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_one_sub_twoProjectionEnergy P hPadj,
    adjoint_one_sub_twoProjectionEnergy R hRadj, hZadj] <;>
    ext x <;> rfl

/-- The zero-mode-subtracted exterior compression kills the removed joint mode on the right. -/
theorem twoProjectionExteriorCompression_mul_zeroMode_eq_zero
    (P R Z : H →L[ℂ] H)
    (hZ : IsIdempotentElem Z)
    (hPZ : P * Z = 0)
    (hRZ : R * Z = 0) :
    twoProjectionExteriorCompression P R Z * Z = 0 := by
  rw [twoProjectionExteriorCompression]
  have hZZ : Z * Z = Z := hZ
  noncomm_ring [hZZ, hPZ, hRZ]

/-- The zero-mode-subtracted exterior compression also kills the removed joint mode on the
left. -/
theorem zeroMode_mul_twoProjectionExteriorCompression_eq_zero
    (P R Z : H →L[ℂ] H)
    (hZ : IsIdempotentElem Z)
    (hZP : Z * P = 0)
    (hZR : Z * R = 0) :
    Z * twoProjectionExteriorCompression P R Z = 0 := by
  rw [twoProjectionExteriorCompression]
  have hZZ : Z * Z = Z := hZ
  noncomm_ring <;>
    simp only [← mul_assoc, hZZ, hZP, hZR, zero_mul, mul_zero, add_zero, zero_add] <;>
    module

/-- After removing the joint zero mode, the exterior overlap splits into its exterior positive
compression minus the adjoint transition channel. -/
theorem twoProjectionExteriorOverlap_eq_exteriorCompression_sub_adjointTransition
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R) :
    twoProjectionExteriorOverlap P R Z =
      twoProjectionExteriorCompression P R Z -
        ContinuousLinearMap.adjoint (twoProjectionTransition P R) := by
  rw [twoProjectionExteriorOverlap, twoProjectionExteriorCompression,
    adjoint_twoProjectionTransition P R hPadj hRadj]
  have hPP : P * P = P := hP
  noncomm_ring [hPP]

/-- The interior Hamiltonian impurity is the positive energy `K†K` of the transition channel.
This is the static supersymmetric factorization behind the prolate number variance. -/
theorem adjoint_twoProjectionTransition_mul_self_eq_interiorCompression_sub_sq
    (P R : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R) :
    ContinuousLinearMap.adjoint (twoProjectionTransition P R) *
        twoProjectionTransition P R =
      twoProjectionInteriorCompression P R -
        twoProjectionInteriorCompression P R * twoProjectionInteriorCompression P R := by
  rw [adjoint_twoProjectionTransition P R hPadj hRadj,
    twoProjectionTransition, twoProjectionInteriorCompression]
  have hPP : P * P = P := hP
  have hRR : R * R = R := hR
  noncomm_ring <;>
    simp only [← mul_assoc, hPP, hRR, zero_mul, mul_zero, add_zero, zero_add] <;>
    module

/-- After subtracting the common zero mode, the exterior Hamiltonian impurity is the partner
positive energy `KK†`. -/
theorem twoProjectionTransition_mul_adjoint_eq_exteriorCompression_sub_sq
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hZ : IsIdempotentElem Z)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPZ : P * Z = 0)
    (hZP : Z * P = 0)
    (hRZ : R * Z = 0)
    (hZR : Z * R = 0) :
    twoProjectionTransition P R *
        ContinuousLinearMap.adjoint (twoProjectionTransition P R) =
      twoProjectionExteriorCompression P R Z -
        twoProjectionExteriorCompression P R Z *
          twoProjectionExteriorCompression P R Z := by
  rw [adjoint_twoProjectionTransition P R hPadj hRadj,
    twoProjectionTransition, twoProjectionExteriorCompression]
  have hPP : P * P = P := hP
  have hRR : R * R = R := hR
  have hZZ : Z * Z = Z := hZ
  noncomm_ring <;>
    simp only [← mul_assoc, hPP, hRR, hZZ, hPZ, hZP, hRZ, hZR,
      zero_mul, mul_zero, add_zero, zero_add] <;>
    module

/-- **Finite Witten supertrace cancellation.**  The interior and exterior Hamiltonian
impurities have exactly the same trace because they are `K†K` and `KK†`.  Only products of
Hilbert--Schmidt operators are traced. -/
theorem opTrace_twoProjectionInteriorCompression_impurity_eq_exteriorCompression_impurity
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hZ : IsIdempotentElem Z)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPZ : P * Z = 0)
    (hZP : Z * P = 0)
    (hRZ : R * Z = 0)
    (hZR : Z * R = 0)
    (hRP : IsHilbertSchmidt (R * P)) :
    opTrace
        (twoProjectionInteriorCompression P R -
          twoProjectionInteriorCompression P R * twoProjectionInteriorCompression P R) =
      opTrace
        (twoProjectionExteriorCompression P R Z -
          twoProjectionExteriorCompression P R Z *
            twoProjectionExteriorCompression P R Z) := by
  have hK : IsHilbertSchmidt (twoProjectionTransition P R) := by
    simpa only [twoProjectionTransition, mul_assoc] using hRP.comp_left (1 - P)
  have hInterior :=
    adjoint_twoProjectionTransition_mul_self_eq_interiorCompression_sub_sq
      P R hP hR hPadj hRadj
  have hExterior :=
    twoProjectionTransition_mul_adjoint_eq_exteriorCompression_sub_sq
      P R Z hP hR hZ hPadj hRadj hPZ hZP hRZ hZR
  calc
    opTrace
        (twoProjectionInteriorCompression P R -
          twoProjectionInteriorCompression P R * twoProjectionInteriorCompression P R) =
        opTrace
          (ContinuousLinearMap.adjoint (twoProjectionTransition P R) *
            twoProjectionTransition P R) := congrArg opTrace hInterior.symm
    _ = opTrace
          (twoProjectionTransition P R *
            ContinuousLinearMap.adjoint (twoProjectionTransition P R)) := by
      simpa only [ContinuousLinearMap.mul_def] using opTrace_comp_comm hK.adjoint hK
    _ = opTrace
        (twoProjectionExteriorCompression P R Z -
          twoProjectionExteriorCompression P R Z *
            twoProjectionExteriorCompression P R Z) := congrArg opTrace hExterior

/-- The transition supercharge intertwines the exterior and interior compressed Hamiltonians. -/
theorem twoProjectionExteriorCompression_mul_transition_eq_transition_mul_interiorCompression
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hZP : Z * P = 0)
    (hZR : Z * R = 0) :
    twoProjectionExteriorCompression P R Z * twoProjectionTransition P R =
      twoProjectionTransition P R * twoProjectionInteriorCompression P R := by
  rw [twoProjectionExteriorCompression, twoProjectionTransition,
    twoProjectionInteriorCompression]
  have hPP : P * P = P := hP
  have hRR : R * R = R := hR
  noncomm_ring <;>
    simp only [← mul_assoc, hPP, hRR, hZP, hZR, zero_mul, mul_zero, add_zero, zero_add] <;>
    module

/-- The transition intertwining persists through every natural power of the partner
Hamiltonians. -/
theorem twoProjectionExteriorCompression_pow_mul_transition_eq_transition_mul_interiorCompression_pow
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hZP : Z * P = 0)
    (hZR : Z * R = 0)
    (n : ℕ) :
    twoProjectionExteriorCompression P R Z ^ n * twoProjectionTransition P R =
      twoProjectionTransition P R * twoProjectionInteriorCompression P R ^ n := by
  have hintertwine :=
    twoProjectionExteriorCompression_mul_transition_eq_transition_mul_interiorCompression
      P R Z hP hR hZP hZR
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        twoProjectionExteriorCompression P R Z ^ (n + 1) *
              twoProjectionTransition P R =
            twoProjectionExteriorCompression P R Z ^ n *
              (twoProjectionExteriorCompression P R Z *
                twoProjectionTransition P R) := by
          rw [pow_succ]
          simp only [mul_assoc]
        _ = twoProjectionExteriorCompression P R Z ^ n *
              (twoProjectionTransition P R *
                twoProjectionInteriorCompression P R) := by rw [hintertwine]
        _ = (twoProjectionExteriorCompression P R Z ^ n *
              twoProjectionTransition P R) *
                twoProjectionInteriorCompression P R := by simp only [mul_assoc]
        _ = (twoProjectionTransition P R *
              twoProjectionInteriorCompression P R ^ n) *
                twoProjectionInteriorCompression P R := by rw [ih]
        _ = twoProjectionTransition P R *
              twoProjectionInteriorCompression P R ^ (n + 1) := by
          rw [pow_succ]
          simp only [mul_assoc]

/-- The `n`th interior power difference factors through the transition supercharge. -/
theorem twoProjectionInteriorCompression_powerDifference_eq_power_mul_adjointTransition_mul_transition
    (P R : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (n : ℕ) :
    twoProjectionInteriorCompression P R ^ (n + 1) -
        twoProjectionInteriorCompression P R ^ (n + 2) =
      (twoProjectionInteriorCompression P R ^ n *
          ContinuousLinearMap.adjoint (twoProjectionTransition P R)) *
        twoProjectionTransition P R := by
  let A := twoProjectionInteriorCompression P R
  let K := twoProjectionTransition P R
  have hImpurity : ContinuousLinearMap.adjoint K * K = A - A * A := by
    simpa only [A, K] using
      adjoint_twoProjectionTransition_mul_self_eq_interiorCompression_sub_sq
        P R hP hR hPadj hRadj
  have hn1 : A ^ n * A = A ^ (n + 1) := by rw [← pow_succ]
  have hn2 : A ^ (n + 1) * A = A ^ (n + 2) := by
    simpa only [Nat.add_assoc] using (pow_succ A (n + 1)).symm
  change A ^ (n + 1) - A ^ (n + 2) = (A ^ n * ContinuousLinearMap.adjoint K) * K
  calc
    A ^ (n + 1) - A ^ (n + 2) = A ^ n * (A - A * A) := by
      rw [← hn2, ← hn1]
      noncomm_ring
    _ = A ^ n * (ContinuousLinearMap.adjoint K * K) := by rw [← hImpurity]
    _ = (A ^ n * ContinuousLinearMap.adjoint K) * K := by simp only [mul_assoc]

/-- The matching exterior power difference factors through the reverse transition. -/
theorem twoProjectionExteriorCompression_powerDifference_eq_power_mul_transition_mul_adjointTransition
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hZ : IsIdempotentElem Z)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPZ : P * Z = 0)
    (hZP : Z * P = 0)
    (hRZ : R * Z = 0)
    (hZR : Z * R = 0)
    (n : ℕ) :
    twoProjectionExteriorCompression P R Z ^ (n + 1) -
        twoProjectionExteriorCompression P R Z ^ (n + 2) =
      (twoProjectionExteriorCompression P R Z ^ n * twoProjectionTransition P R) *
        ContinuousLinearMap.adjoint (twoProjectionTransition P R) := by
  let E := twoProjectionExteriorCompression P R Z
  let K := twoProjectionTransition P R
  have hImpurity : K * ContinuousLinearMap.adjoint K = E - E * E := by
    simpa only [E, K] using
      twoProjectionTransition_mul_adjoint_eq_exteriorCompression_sub_sq
        P R Z hP hR hZ hPadj hRadj hPZ hZP hRZ hZR
  have hn1 : E ^ n * E = E ^ (n + 1) := by rw [← pow_succ]
  have hn2 : E ^ (n + 1) * E = E ^ (n + 2) := by
    simpa only [Nat.add_assoc] using (pow_succ E (n + 1)).symm
  change E ^ (n + 1) - E ^ (n + 2) = (E ^ n * K) * ContinuousLinearMap.adjoint K
  calc
    E ^ (n + 1) - E ^ (n + 2) = E ^ n * (E - E * E) := by
      rw [← hn2, ← hn1]
      noncomm_ring
    _ = E ^ n * (K * ContinuousLinearMap.adjoint K) := by rw [← hImpurity]
    _ = (E ^ n * K) * ContinuousLinearMap.adjoint K := by simp only [mul_assoc]

/-- **All-power Witten supertrace cancellation.**  Every consecutive power difference of the
interior Hamiltonian has the same trace as its exterior partner.  This is the exact telescoping
input needed to reduce equality of their Hilbert--Schmidt energies to decay of the terminal power
traces. -/
theorem opTrace_twoProjectionInteriorCompression_powerDifference_eq_exteriorCompression_powerDifference
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hZ : IsIdempotentElem Z)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPZ : P * Z = 0)
    (hZP : Z * P = 0)
    (hRZ : R * Z = 0)
    (hZR : Z * R = 0)
    (hRP : IsHilbertSchmidt (R * P))
    (n : ℕ) :
    opTrace
        (twoProjectionInteriorCompression P R ^ (n + 1) -
          twoProjectionInteriorCompression P R ^ (n + 2)) =
      opTrace
        (twoProjectionExteriorCompression P R Z ^ (n + 1) -
          twoProjectionExteriorCompression P R Z ^ (n + 2)) := by
  let A := twoProjectionInteriorCompression P R
  let E := twoProjectionExteriorCompression P R Z
  let K := twoProjectionTransition P R
  have hK : IsHilbertSchmidt K := by
    simpa only [K, twoProjectionTransition, mul_assoc] using hRP.comp_left (1 - P)
  have hAK : IsHilbertSchmidt (A ^ n * ContinuousLinearMap.adjoint K) := by
    exact hK.adjoint.comp_left (A ^ n)
  have hintertwine : E ^ n * K = K * A ^ n := by
    simpa only [A, E, K] using
      twoProjectionExteriorCompression_pow_mul_transition_eq_transition_mul_interiorCompression_pow
        P R Z hP hR hZP hZR n
  have hInterior :
      A ^ (n + 1) - A ^ (n + 2) =
        (A ^ n * ContinuousLinearMap.adjoint K) * K := by
    simpa only [A, K] using
      twoProjectionInteriorCompression_powerDifference_eq_power_mul_adjointTransition_mul_transition
        P R hP hR hPadj hRadj n
  have hExterior :
      E ^ (n + 1) - E ^ (n + 2) =
        (E ^ n * K) * ContinuousLinearMap.adjoint K := by
    simpa only [E, K] using
      twoProjectionExteriorCompression_powerDifference_eq_power_mul_transition_mul_adjointTransition
        P R Z hP hR hZ hPadj hRadj hPZ hZP hRZ hZR n
  calc
    opTrace (A ^ (n + 1) - A ^ (n + 2)) =
        opTrace ((A ^ n * ContinuousLinearMap.adjoint K) * K) :=
      congrArg opTrace hInterior
    _ = opTrace (K * (A ^ n * ContinuousLinearMap.adjoint K)) := by
      simpa only [ContinuousLinearMap.mul_def] using opTrace_comp_comm hAK hK
    _ = opTrace ((K * A ^ n) * ContinuousLinearMap.adjoint K) := by
      simp only [mul_assoc]
    _ = opTrace ((E ^ n * K) * ContinuousLinearMap.adjoint K) := by
      rw [hintertwine]
    _ = opTrace (E ^ (n + 1) - E ^ (n + 2)) :=
      congrArg opTrace hExterior.symm

/-- **Finite telescoping invariant.**  Once the two compressed Hamiltonians are
Hilbert--Schmidt, the difference of their individual power traces is independent of the power
from degree two onward.  Consequently, proving terminal power-trace decay is sufficient to
identify their squared Hilbert--Schmidt energies. -/
theorem opTrace_twoProjectionInteriorCompression_sq_sub_exteriorCompression_sq_eq_power_sub_power
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hZ : IsIdempotentElem Z)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPZ : P * Z = 0)
    (hZP : Z * P = 0)
    (hRZ : R * Z = 0)
    (hZR : Z * R = 0)
    (hRP : IsHilbertSchmidt (R * P))
    (hE : IsHilbertSchmidt (twoProjectionExteriorCompression P R Z))
    (n : ℕ) :
    opTrace (twoProjectionInteriorCompression P R ^ 2) -
        opTrace (twoProjectionExteriorCompression P R Z ^ 2) =
      opTrace (twoProjectionInteriorCompression P R ^ (n + 2)) -
        opTrace (twoProjectionExteriorCompression P R Z ^ (n + 2)) := by
  let A := twoProjectionInteriorCompression P R
  let E := twoProjectionExteriorCompression P R Z
  have hA : IsHilbertSchmidt A := by
    simpa only [A, twoProjectionInteriorCompression, mul_assoc] using hRP.comp_left P
  change opTrace (A ^ 2) - opTrace (E ^ 2) =
    opTrace (A ^ (n + 2)) - opTrace (E ^ (n + 2))
  induction n with
  | zero => simp
  | succ n ih =>
      have hPowerDifference :=
        opTrace_twoProjectionInteriorCompression_powerDifference_eq_exteriorCompression_powerDifference
          P R Z hP hR hZ hPadj hRadj hPZ hZP hRZ hZR hRP (n + 1)
      have hAlinear := opTrace_pow_add_two_sub_pow_add_three_of_isHilbertSchmidt A hA n
      have hElinear := opTrace_pow_add_two_sub_pow_add_three_of_isHilbertSchmidt E hE n
      have hstep :
          opTrace (A ^ (n + 2)) - opTrace (E ^ (n + 2)) =
            opTrace (A ^ (n + 3)) - opTrace (E ^ (n + 3)) := by
        change opTrace (A ^ (n + 2) - A ^ (n + 3)) =
            opTrace (E ^ (n + 2) - E ^ (n + 3)) at hPowerDifference
        rw [hAlinear, hElinear] at hPowerDifference
        linear_combination hPowerDifference
      calc
        opTrace (A ^ 2) - opTrace (E ^ 2) =
            opTrace (A ^ (n + 2)) - opTrace (E ^ (n + 2)) := ih
        _ = opTrace (A ^ (n + 3)) - opTrace (E ^ (n + 3)) := hstep
        _ = opTrace (A ^ (Nat.succ n + 2)) -
            opTrace (E ^ (Nat.succ n + 2)) := by
          simp only [Nat.succ_eq_add_one, Nat.add_assoc]

/-- The zero-mode-corrected complement is the difference of the interior and exterior overlap
channels. -/
theorem twoProjection_correctedComplement_eq_overlap_sub_exterior
    (P R Z : H →L[ℂ] H) :
    Z - (1 - P - R) = R * P - twoProjectionExteriorOverlap P R Z := by
  rw [twoProjectionExteriorOverlap]
  noncomm_ring

/-- If the corrected complement and the interior overlap are Hilbert--Schmidt, then so is the
zero-mode-subtracted exterior overlap. -/
theorem twoProjectionExteriorOverlap_isHilbertSchmidt
    (P R Z : H →L[ℂ] H)
    (hC : IsHilbertSchmidt (Z - (1 - P - R)))
    (hRP : IsHilbertSchmidt (R * P)) :
    IsHilbertSchmidt (twoProjectionExteriorOverlap P R Z) := by
  have hEq : twoProjectionExteriorOverlap P R Z = R * P - (Z - (1 - P - R)) := by
    rw [twoProjectionExteriorOverlap]
    noncomm_ring
  rw [hEq]
  exact hRP.sub hC

/-- The interior overlap `RP` is Hilbert--Schmidt orthogonal to the corrected exterior overlap.
Only the projection law for `R`, self-adjointness of `P,R`, and removal of the `R`-zero mode are
used. -/
theorem hsInner_twoProjection_overlap_exterior_eq_zero
    (P R Z : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hRZ : R * Z = 0) :
    hsInner (R * P) (twoProjectionExteriorOverlap P R Z) = 0 := by
  have hAdj : ContinuousLinearMap.adjoint (R * P) = P * R := by
    change ContinuousLinearMap.adjoint (R ∘L P) = P ∘L R
    rw [ContinuousLinearMap.adjoint_comp, hPadj, hRadj]
  have hzero :
      ContinuousLinearMap.adjoint (R * P) ∘L
          twoProjectionExteriorOverlap P R Z = 0 := by
    rw [hAdj]
    change (P * R) * ((1 - R) * (1 - P) - Z) = 0
    have hRR : R * R = R := hR
    noncomm_ring <;>
      simp only [← mul_assoc, hRR, hRZ, zero_mul, mul_zero, add_zero, zero_add] <;>
      module
  have htrace :
      opTrace
          (ContinuousLinearMap.adjoint (R * P) ∘L
            twoProjectionExteriorOverlap P R Z) =
        hsInner (R * P) (twoProjectionExteriorOverlap P R Z) := by
    simpa using opTrace_comp_eq_hsInner
      (ContinuousLinearMap.adjoint (R * P))
      (twoProjectionExteriorOverlap P R Z)
  calc
    hsInner (R * P) (twoProjectionExteriorOverlap P R Z) =
        opTrace
          (ContinuousLinearMap.adjoint (R * P) ∘L
            twoProjectionExteriorOverlap P R Z) := htrace.symm
    _ = opTrace 0 := congrArg opTrace hzero
    _ = 0 := by simp [opTrace]

/-- **Two-projection Hilbert--Schmidt energy split.**  The energy of the zero-mode-corrected
supersymmetric partner is exactly the sum of its interior and exterior transition energies.
This replaces an opaque correction norm by two positive overlap values. -/
theorem hsNormSq_twoProjection_correctedComplement_eq_overlap_add_exterior
    (P R Z : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hRZ : R * Z = 0)
    (hC : IsHilbertSchmidt (Z - (1 - P - R)))
    (hRP : IsHilbertSchmidt (R * P)) :
    hsNormSq (Z - (1 - P - R)) =
      hsNormSq (R * P) + hsNormSq (twoProjectionExteriorOverlap P R Z) := by
  have hD := twoProjectionExteriorOverlap_isHilbertSchmidt P R Z hC hRP
  have horth := hsInner_twoProjection_overlap_exterior_eq_zero
    P R Z hR hPadj hRadj hRZ
  rw [twoProjection_correctedComplement_eq_overlap_sub_exterior]
  exact hsNormSq_sub_eq_add_of_hsInner_eq_zero hRP hD horth

/-- The interior compression inherits the Hilbert--Schmidt property from the overlap. -/
theorem twoProjectionInteriorCompression_isHilbertSchmidt
    (P R : H →L[ℂ] H) (hRP : IsHilbertSchmidt (R * P)) :
    IsHilbertSchmidt (twoProjectionInteriorCompression P R) := by
  simpa only [twoProjectionInteriorCompression, mul_assoc] using hRP.comp_left P

/-- The transition corner inherits the Hilbert--Schmidt property from the overlap. -/
theorem twoProjectionTransition_isHilbertSchmidt
    (P R : H →L[ℂ] H) (hRP : IsHilbertSchmidt (R * P)) :
    IsHilbertSchmidt (twoProjectionTransition P R) := by
  simpa only [twoProjectionTransition, mul_assoc] using hRP.comp_left (1 - P)

/-- The exterior compression is Hilbert--Schmidt once the exterior overlap and the paired
transition are.  This is the ideal-theoretic content of the exterior supersymmetric split. -/
theorem twoProjectionExteriorCompression_isHilbertSchmidt
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hRP : IsHilbertSchmidt (R * P))
    (hD : IsHilbertSchmidt (twoProjectionExteriorOverlap P R Z)) :
    IsHilbertSchmidt (twoProjectionExteriorCompression P R Z) := by
  have hK := twoProjectionTransition_isHilbertSchmidt P R hRP
  have hsplit :=
    twoProjectionExteriorOverlap_eq_exteriorCompression_sub_adjointTransition
      P R Z hP hPadj hRadj
  have hEq :
      twoProjectionExteriorCompression P R Z =
        twoProjectionExteriorOverlap P R Z +
          ContinuousLinearMap.adjoint (twoProjectionTransition P R) := by
    rw [hsplit]
    abel
  rw [hEq]
  exact hD.add hK.adjoint

/-- **Interior supercharge energy split.**  The overlap energy is the sum of the positive
compression energy and the transition energy.  For a Fermi projection this is
`Tr(T) = Tr(T²) + Tr(T(1-T))`, proved without taking the trace of a lone Hilbert--Schmidt
operator. -/
theorem hsNormSq_twoProjection_overlap_eq_interiorCompression_add_transition
    (P R : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hRP : IsHilbertSchmidt (R * P)) :
    hsNormSq (R * P) =
      hsNormSq (twoProjectionInteriorCompression P R) +
        hsNormSq (twoProjectionTransition P R) := by
  have hA := twoProjectionInteriorCompression_isHilbertSchmidt P R hRP
  have hK := twoProjectionTransition_isHilbertSchmidt P R hRP
  have hAadj :
      ContinuousLinearMap.adjoint (twoProjectionInteriorCompression P R) =
        twoProjectionInteriorCompression P R :=
    adjoint_twoProjectionInteriorCompression P R hPadj hRadj
  have hzero :
      ContinuousLinearMap.adjoint (twoProjectionInteriorCompression P R) ∘L
          twoProjectionTransition P R = 0 := by
    rw [hAadj]
    change twoProjectionInteriorCompression P R * twoProjectionTransition P R = 0
    rw [twoProjectionInteriorCompression, twoProjectionTransition]
    have hPP : P * P = P := hP
    noncomm_ring <;>
      simp only [← mul_assoc, hPP, zero_mul, mul_zero, add_zero, zero_add] <;>
      module
  have horth :
      hsInner (twoProjectionInteriorCompression P R)
          (twoProjectionTransition P R) = 0 :=
    hsInner_eq_zero_of_adjoint_comp_eq_zero _ _ hzero
  rw [twoProjection_overlap_eq_interiorCompression_add_transition]
  exact hsNormSq_add_eq_of_hsInner_eq_zero hA hK horth

/-- **Exterior supercharge energy split.**  Removing the common zero mode leaves the exterior
compression and the adjoint transition in orthogonal `P` sectors.  Hence the exterior-overlap
energy is their exact sum. -/
theorem hsNormSq_twoProjectionExteriorOverlap_eq_exteriorCompression_add_transition
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hZadj : ContinuousLinearMap.adjoint Z = Z)
    (hZP : Z * P = 0)
    (hRP : IsHilbertSchmidt (R * P))
    (hD : IsHilbertSchmidt (twoProjectionExteriorOverlap P R Z)) :
    hsNormSq (twoProjectionExteriorOverlap P R Z) =
      hsNormSq (twoProjectionExteriorCompression P R Z) +
        hsNormSq (twoProjectionTransition P R) := by
  have hK := twoProjectionTransition_isHilbertSchmidt P R hRP
  have hE := twoProjectionExteriorCompression_isHilbertSchmidt
    P R Z hP hPadj hRadj hRP hD
  have hKadj := adjoint_twoProjectionTransition P R hPadj hRadj
  have hEadj :
      ContinuousLinearMap.adjoint (twoProjectionExteriorCompression P R Z) =
        twoProjectionExteriorCompression P R Z :=
    adjoint_twoProjectionExteriorCompression P R Z hPadj hRadj hZadj
  have hzero :
      ContinuousLinearMap.adjoint (twoProjectionExteriorCompression P R Z) ∘L
          ContinuousLinearMap.adjoint (twoProjectionTransition P R) = 0 := by
    rw [hEadj, hKadj]
    change twoProjectionExteriorCompression P R Z * (P * R * (1 - P)) = 0
    rw [twoProjectionExteriorCompression]
    have hPP : P * P = P := hP
    noncomm_ring <;>
      simp only [← mul_assoc, hPP, hZP, zero_mul, mul_zero, add_zero, zero_add] <;>
      module
  have horth :
      hsInner (twoProjectionExteriorCompression P R Z)
          (ContinuousLinearMap.adjoint (twoProjectionTransition P R)) = 0 :=
    hsInner_eq_zero_of_adjoint_comp_eq_zero _ _ hzero
  rw [twoProjectionExteriorOverlap_eq_exteriorCompression_sub_adjointTransition
    P R Z hP hPadj hRadj]
  calc
    hsNormSq
          (twoProjectionExteriorCompression P R Z -
            ContinuousLinearMap.adjoint (twoProjectionTransition P R)) =
        hsNormSq (twoProjectionExteriorCompression P R Z) +
          hsNormSq (ContinuousLinearMap.adjoint (twoProjectionTransition P R)) :=
      hsNormSq_sub_eq_add_of_hsInner_eq_zero hE hK.adjoint horth
    _ = hsNormSq (twoProjectionExteriorCompression P R Z) +
          hsNormSq (twoProjectionTransition P R) := by
      rw [hK.hsNormSq_adjoint]

/-- **Finite Witten-index descent.**  The same off-diagonal supercharge energy occurs in the
interior and exterior sector splits, so it cancels from their difference.  Equivalently, the
unresolved equality of the two overlap energies is reduced exactly to equality of the two
positive compressed Hamiltonian energies.  This is finite and algebraic: no spectral pairing or
limiting trace is used. -/
theorem hsNormSq_twoProjection_overlap_add_exteriorCompression_eq_exteriorOverlap_add_interiorCompression
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hZadj : ContinuousLinearMap.adjoint Z = Z)
    (hZP : Z * P = 0)
    (hRP : IsHilbertSchmidt (R * P))
    (hD : IsHilbertSchmidt (twoProjectionExteriorOverlap P R Z)) :
    hsNormSq (R * P) + hsNormSq (twoProjectionExteriorCompression P R Z) =
      hsNormSq (twoProjectionExteriorOverlap P R Z) +
        hsNormSq (twoProjectionInteriorCompression P R) := by
  have hInterior := hsNormSq_twoProjection_overlap_eq_interiorCompression_add_transition
    P R hP hPadj hRadj hRP
  have hExterior :=
    hsNormSq_twoProjectionExteriorOverlap_eq_exteriorCompression_add_transition
      P R Z hP hPadj hRadj hZadj hZP hRP hD
  rw [hInterior, hExterior]
  ring

/-- **Zero-mode-subtracted supersymmetric partition.**  The full corrected-complement energy is
the sum of the interior and exterior compressed Hamiltonian energies plus twice the transition
energy.  In free-fermion language the last term is twice the number variance. -/
theorem hsNormSq_twoProjection_correctedComplement_eq_compressions_add_two_mul_transition
    (P R Z : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hZadj : ContinuousLinearMap.adjoint Z = Z)
    (hZP : Z * P = 0)
    (hRZ : R * Z = 0)
    (hC : IsHilbertSchmidt (Z - (1 - P - R)))
    (hRP : IsHilbertSchmidt (R * P)) :
    hsNormSq (Z - (1 - P - R)) =
      hsNormSq (twoProjectionInteriorCompression P R) +
        hsNormSq (twoProjectionExteriorCompression P R Z) +
          2 * hsNormSq (twoProjectionTransition P R) := by
  have hD := twoProjectionExteriorOverlap_isHilbertSchmidt P R Z hC hRP
  have hCorrection :=
    hsNormSq_twoProjection_correctedComplement_eq_overlap_add_exterior
      P R Z hR hPadj hRadj hRZ hC hRP
  have hInterior := hsNormSq_twoProjection_overlap_eq_interiorCompression_add_transition
    P R hP hPadj hRadj hRP
  have hExterior :=
    hsNormSq_twoProjectionExteriorOverlap_eq_exteriorCompression_add_transition
      P R Z hP hPadj hRadj hZadj hZP hRP hD
  rw [hCorrection, hInterior, hExterior]
  ring

end HTGeometry
