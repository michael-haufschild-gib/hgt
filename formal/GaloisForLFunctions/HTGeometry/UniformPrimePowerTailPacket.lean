import GaloisForLFunctions.HTGeometry.PrimePowerDynamicCoefficientField

/-!
# Uniform finite dilation towers from layerwise tail independence

For finitely many dilation layers and one finite source alphabet, layerwise tail independence
produces evaluation packets which are simultaneously nonsingular and globally prime-disjoint.
The resulting exponent-block determinant is the determinant of a block-diagonal matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- A nonsingular evaluation packet cannot repeat an evaluation point. -/
theorem evaluationPacket_injective_of_isUnit
    {A P : Type*} [Fintype A] [DecidableEq A]
    (a : A → P → ℂ) (points : A → P)
    (hunit : IsUnit (Matrix.of fun row col => a col (points row) : Matrix A A ℂ)) :
    Function.Injective points := by
  intro i j hij
  by_contra hne
  have hdetne : (Matrix.of fun row col => a col (points row) : Matrix A A ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  apply hdetne
  apply Matrix.det_zero_of_row_eq hne
  funext col
  simp [Matrix.of_apply, hij]

/-- Simultaneous layer packets: every layer matrix is invertible, all chosen primes are globally
distinct, and every chosen prime avoids the prescribed finite set. -/
theorem exists_disjoint_uniform_layer_packets
    {A : Type*} [Fintype A] [DecidableEq A]
    (d : ℕ) (a : Fin d → A → Nat.Primes → ℂ)
    (htail : ∀ r, TailCoefficientIndependent (a r))
    (forbidden : Set Nat.Primes) (hforbidden : forbidden.Finite) :
    ∃ q : A × Fin d → Nat.Primes,
      Function.Injective q ∧
      (∀ i, q i ∉ forbidden) ∧
      ∀ r, IsUnit
        (Matrix.of (fun row col => a r col (q (row, r))) : Matrix A A ℂ) := by
  induction d generalizing forbidden with
  | zero =>
      refine ⟨fun x => Fin.elim0 x.2, ?_, ?_, ?_⟩
      · intro x
        exact Fin.elim0 x.2
      · intro x
        exact Fin.elim0 x.2
      · intro r
        exact Fin.elim0 r
  | succ d ih =>
      let a0 : Fin d → A → Nat.Primes → ℂ := fun r => a r.castSucc
      have htail0 : ∀ r, TailCoefficientIndependent (a0 r) := fun r => htail r.castSucc
      obtain ⟨q0, hq0, havoid0, hunit0⟩ :=
        ih a0 htail0 forbidden hforbidden
      let used : Set Nat.Primes := Set.range q0
      have hused : used.Finite := Set.finite_range q0
      let forbiddenLast : Set Nat.Primes := forbidden ∪ used
      have hforbiddenLast : forbiddenLast.Finite := hforbidden.union hused
      obtain ⟨qLast, havoidLast, hunitLast⟩ :=
        TailCoefficientIndependent.exists_fullRank_evaluation_packet_avoiding
          (a (Fin.last d)) (htail (Fin.last d)) forbiddenLast hforbiddenLast
      have hqLast : Function.Injective qLast :=
        evaluationPacket_injective_of_isUnit (a (Fin.last d)) qLast hunitLast
      let q : A × Fin (d + 1) → Nat.Primes := fun x =>
        Fin.lastCases (qLast x.1) (fun r => q0 (x.1, r)) x.2
      refine ⟨q, ?_, ?_, ?_⟩
      · rintro ⟨x, r⟩ ⟨y, s⟩ hxy
        induction r using Fin.lastCases with
        | last =>
            induction s using Fin.lastCases with
            | last =>
                have h : x = y := hqLast (by simpa [q] using hxy)
                subst y
                rfl
            | cast s =>
                exfalso
                apply havoidLast x
                apply Set.mem_union_right forbidden
                exact ⟨(y, s), by simpa [q] using hxy.symm⟩
        | cast r =>
            induction s using Fin.lastCases with
            | last =>
                exfalso
                apply havoidLast y
                apply Set.mem_union_right forbidden
                exact ⟨(x, r), by simpa [q] using hxy⟩
            | cast s =>
                have h : (x, r) = (y, s) := hq0 (by simpa [q] using hxy)
                cases h
                rfl
      · rintro ⟨x, r⟩
        induction r using Fin.lastCases with
        | last =>
            intro hx
            apply havoidLast x
            apply Set.mem_union_left used
            simpa [q] using hx
        | cast r =>
            simpa [q] using havoid0 (x, r)
      · intro r
        induction r using Fin.lastCases with
        | last => simpa [q] using hunitLast
        | cast r => simpa [q, a0] using hunit0 r

/-- Exponent of a source in the uniform `d`-layer tower. -/
def uniformPrimePowerExponent {A : Type*} {d : ℕ} : A × Fin d → ℕ :=
  fun i => i.2

/-- Flatten a layer-indexed source alphabet into one family. -/
def uniformPrimePowerCoefficient
    {A : Type*} {d : ℕ} (a : Fin d → A → Nat.Primes → ℂ) :
    A × Fin d → Nat.Primes → ℂ :=
  fun i => a i.2 i.1

/-- **Uniform prime-power tail packet law.**  Layerwise tail independence discharges the cofinite
packet hypothesis for every finite dilation tower. -/
theorem cofinitePrimePowerPacket_of_uniform_layerwise_tailIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (d : ℕ) (a : Fin d → A → Nat.Primes → ℂ)
    (htail : ∀ r, TailCoefficientIndependent (a r)) :
    CofinitePrimePowerPacket
      (uniformPrimePowerExponent (A := A) (d := d))
      (uniformPrimePowerCoefficient a) := by
  intro forbidden hforbidden
  obtain ⟨q, hq, havoid, hunit⟩ :=
    exists_disjoint_uniform_layer_packets d a htail forbidden hforbidden
  refine ⟨q, hq, havoid, ?_⟩
  let E : Fin d → Matrix A A ℂ := fun r =>
    Matrix.of fun row col => a r col (q (row, r))
  let C : Fin d → Matrix A A ℂ := fun r =>
    (((r : ℕ) + 1 : ℕ) : ℂ) • E r
  have hmatrix :
      primePowerBlockMatrix
          (uniformPrimePowerExponent (A := A) (d := d))
          (primePowerPacketCoefficientMatrix
            (uniformPrimePowerExponent (A := A) (d := d))
            (uniformPrimePowerCoefficient a) q) =
        Matrix.blockDiagonal C := by
    ext i j
    rcases i with ⟨i, r⟩
    rcases j with ⟨j, s⟩
    by_cases hrs : r = s
    · subst s
      simp [primePowerBlockMatrix, primePowerPacketCoefficientMatrix,
        uniformPrimePowerExponent, uniformPrimePowerCoefficient,
        Matrix.blockDiagonal, C, E]
    · have hrsNat : (r : ℕ) ≠ (s : ℕ) := by
        intro h
        exact hrs (Fin.ext h)
      simp [primePowerBlockMatrix, uniformPrimePowerExponent,
        Matrix.blockDiagonal, C, E, hrs, hrsNat]
  rw [hmatrix, Matrix.det_blockDiagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  rw [show C r = (((r : ℕ) + 1 : ℕ) : ℂ) • E r from rfl,
    Matrix.det_smul]
  apply mul_ne_zero
  · apply pow_ne_zero
    exact_mod_cast Nat.succ_ne_zero (r : ℕ)
  · exact ((Matrix.isUnit_iff_isUnit_det _).mp (hunit r)).ne_zero

/-- The uniform finite dilation tower is algebraically independent over the intrinsic finite-prime
coefficient field. -/
theorem algebraicIndependent_uniformPrimePowerTower_over_finitePrimeCoefficientField
    {A : Type*} [Fintype A] [DecidableEq A]
    (d : ℕ) (a : Fin d → A → Nat.Primes → ℂ)
    (htail : ∀ r, TailCoefficientIndependent (a r)) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun i : A × Fin d =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimePowerColumn
            (uniformPrimePowerExponent i)
            (uniformPrimePowerCoefficient a i))) :=
  algebraicIndependent_fractionPrimePowerColumns_over_finitePrimeCoefficientField
    (uniformPrimePowerExponent (A := A) (d := d))
    (uniformPrimePowerCoefficient a)
    (cofinitePrimePowerPacket_of_uniform_layerwise_tailIndependent d a htail)

end

end GaloisForLFunctions.HTGeometry
