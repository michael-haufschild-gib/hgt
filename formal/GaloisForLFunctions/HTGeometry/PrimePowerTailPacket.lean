import GaloisForLFunctions.HTGeometry.UniformPrimePowerTailPacket

/-!
# Nonuniform finite prime-power towers

The source alphabet may vary with the dilation layer.  The global index is the dependent sum
`Σ r, A r`, so the total differential rank is the sum of the layer cardinalities.  Layer packets
are chosen recursively outside the primes already used by earlier layers.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

universe u

/-- Simultaneous prime-disjoint packets for a nonuniform finite family of layers. -/
theorem exists_disjoint_layer_packets
    (d : ℕ) (A : Fin d → Type u)
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (a : ∀ r, A r → Nat.Primes → ℂ)
    (htail : ∀ r, TailCoefficientIndependent (a r))
    (forbidden : Set Nat.Primes) (hforbidden : forbidden.Finite) :
    ∃ q : (Σ r, A r) → Nat.Primes,
      Function.Injective q ∧
      (∀ i, q i ∉ forbidden) ∧
      ∀ r, IsUnit
        (Matrix.of (fun row col => a r col (q ⟨r, row⟩)) : Matrix (A r) (A r) ℂ) := by
  induction d generalizing forbidden with
  | zero =>
      refine ⟨fun x => Fin.elim0 x.1, ?_, ?_, ?_⟩
      · intro x
        exact Fin.elim0 x.1
      · intro x
        exact Fin.elim0 x.1
      · intro r
        exact Fin.elim0 r
  | succ d ih =>
      let A0 : Fin d → Type u := fun r => A r.castSucc
      letI (r : Fin d) : Fintype (A0 r) := inferInstance
      letI (r : Fin d) : DecidableEq (A0 r) := inferInstance
      let a0 : ∀ r, A0 r → Nat.Primes → ℂ := fun r => a r.castSucc
      have htail0 : ∀ r, TailCoefficientIndependent (a0 r) := fun r => htail r.castSucc
      obtain ⟨q0, hq0, havoid0, hunit0⟩ :=
        ih A0 a0 htail0 forbidden hforbidden
      let used : Set Nat.Primes := Set.range q0
      have hused : used.Finite := Set.finite_range q0
      let forbiddenLast : Set Nat.Primes := forbidden ∪ used
      have hforbiddenLast : forbiddenLast.Finite := hforbidden.union hused
      obtain ⟨qLast, havoidLast, hunitLast⟩ :=
        TailCoefficientIndependent.exists_fullRank_evaluation_packet_avoiding
          (a (Fin.last d)) (htail (Fin.last d)) forbiddenLast hforbiddenLast
      have hqLast : Function.Injective qLast :=
        evaluationPacket_injective_of_isUnit (a (Fin.last d)) qLast hunitLast
      let qByLayer : ∀ r : Fin (d + 1), A r → Nat.Primes :=
        Fin.lastCases qLast (fun r (y : A r.castSucc) => q0 ⟨r, y⟩)
      let q : (Σ r, A r) → Nat.Primes := fun x =>
        qByLayer x.1 x.2
      refine ⟨q, ?_, ?_, ?_⟩
      · rintro ⟨r, x⟩ ⟨s, y⟩ hxy
        induction r using Fin.lastCases with
        | last =>
            induction s using Fin.lastCases with
            | last =>
                have h : x = y := hqLast (by simpa [q, qByLayer] using hxy)
                subst y
                rfl
            | cast s =>
                exfalso
                apply havoidLast x
                apply Set.mem_union_right forbidden
                exact ⟨⟨s, y⟩, by simpa [q, qByLayer] using hxy.symm⟩
        | cast r =>
            induction s using Fin.lastCases with
            | last =>
                exfalso
                apply havoidLast y
                apply Set.mem_union_right forbidden
                exact ⟨⟨r, x⟩, by simpa [q, qByLayer] using hxy⟩
            | cast s =>
                have h : (⟨r, x⟩ : Σ r, A0 r) = ⟨s, y⟩ :=
                  hq0 (by simpa [q, qByLayer, A0] using hxy)
                cases h
                rfl
      · rintro ⟨r, x⟩
        induction r using Fin.lastCases with
        | last =>
            intro hx
            apply havoidLast x
            apply Set.mem_union_left used
            simpa [q, qByLayer] using hx
        | cast r =>
            simpa [q, qByLayer, A0] using havoid0 (⟨r, x⟩ : Σ r, A0 r)
      · intro r
        induction r using Fin.lastCases with
        | last => simpa [q, qByLayer] using hunitLast
        | cast r => simpa [q, qByLayer, A0, a0] using hunit0 r

/-- Exponent of a source in a nonuniform finite tower. -/
def primePowerSigmaExponent
    {d : ℕ} {A : Fin d → Type u} : (Σ r, A r) → ℕ :=
  fun i => i.1

/-- Flatten a dependent layer-indexed coefficient family. -/
def primePowerSigmaCoefficient
    {d : ℕ} {A : Fin d → Type u}
    (a : ∀ r, A r → Nat.Primes → ℂ) :
    (Σ r, A r) → Nat.Primes → ℂ :=
  fun i => a i.1 i.2

/-- **Nonuniform prime-power tail packet law.**  For finite layer alphabets `A r`, layerwise tail
independence supplies cofinite nonsingular packets on the total family `Σ r, A r`. -/
theorem cofinitePrimePowerPacket_of_layerwise_tailIndependent
    (d : ℕ) (A : Fin d → Type u)
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (a : ∀ r, A r → Nat.Primes → ℂ)
    (htail : ∀ r, TailCoefficientIndependent (a r)) :
    CofinitePrimePowerPacket
      (primePowerSigmaExponent (A := A))
      (primePowerSigmaCoefficient a) := by
  intro forbidden hforbidden
  obtain ⟨q, hq, havoid, hunit⟩ :=
    exists_disjoint_layer_packets d A a htail forbidden hforbidden
  refine ⟨q, hq, havoid, ?_⟩
  let E : ∀ r, Matrix (A r) (A r) ℂ := fun r =>
    Matrix.of fun row col => a r col (q ⟨r, row⟩)
  let C : ∀ r, Matrix (A r) (A r) ℂ := fun r =>
    (((r : ℕ) + 1 : ℕ) : ℂ) • E r
  have hmatrix :
      primePowerBlockMatrix
          (primePowerSigmaExponent (A := A))
          (primePowerPacketCoefficientMatrix
            (primePowerSigmaExponent (A := A))
            (primePowerSigmaCoefficient a) q) =
        Matrix.blockDiagonal' C := by
    ext i j
    rcases i with ⟨r, i⟩
    rcases j with ⟨s, j⟩
    by_cases hrs : r = s
    · subst s
      simp [primePowerBlockMatrix, primePowerPacketCoefficientMatrix,
        primePowerSigmaExponent, primePowerSigmaCoefficient,
        Matrix.blockDiagonal', C, E]
    · have hrsNat : (r : ℕ) ≠ (s : ℕ) := by
        intro h
        exact hrs (Fin.ext h)
      simp [primePowerBlockMatrix, primePowerSigmaExponent,
        Matrix.blockDiagonal', C, E, hrs, hrsNat]
  rw [hmatrix]
  have hC : ∀ r, IsUnit (C r) := by
    intro r
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    rw [show C r = (((r : ℕ) + 1 : ℕ) : ℂ) • E r from rfl,
      Matrix.det_smul]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact_mod_cast Nat.succ_ne_zero (r : ℕ)
    · exact ((Matrix.isUnit_iff_isUnit_det _).mp (hunit r)).ne_zero
  have hPi : IsUnit C := Pi.isUnit_iff.mpr hC
  have hBlock : IsUnit (Matrix.blockDiagonal' C) :=
    hPi.map (Matrix.blockDiagonal'RingHom (fun r => A r) ℂ)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hBlock).ne_zero

/-- **Nonuniform finite prime-power tower theorem.**  The total family is algebraically independent
over the finite-prime coefficient field; consequently its differential transcendence rank is the
sum of the cardinalities of the layer alphabets. -/
theorem algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField
    (d : ℕ) (A : Fin d → Type u)
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (a : ∀ r, A r → Nat.Primes → ℂ)
    (htail : ∀ r, TailCoefficientIndependent (a r)) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun i : Σ r, A r =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimePowerColumn
            (primePowerSigmaExponent i)
            (primePowerSigmaCoefficient a i))) :=
  algebraicIndependent_fractionPrimePowerColumns_over_finitePrimeCoefficientField
    (primePowerSigmaExponent (A := A))
    (primePowerSigmaCoefficient a)
    (cofinitePrimePowerPacket_of_layerwise_tailIndependent d A a htail)

end

end GaloisForLFunctions.HTGeometry
