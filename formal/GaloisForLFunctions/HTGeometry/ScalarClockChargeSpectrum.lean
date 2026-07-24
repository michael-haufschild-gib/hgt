import GaloisForLFunctions.HTGeometry.ScalarProperSubfieldClockInvariant

/-!
# Every positive clock charge is realized

The clock-character law attaches to each nonconstant persistent core a nonnegative integer charge `k`,
and at `k > 0` the core is `C⟨q⟩` with `ρ_λ(q) = λ^k·q`.  This file shows the charge spectrum is the
full set of positive integers: for every `k ≥ 1` the `k`-th differential jet `y^(k) = X_{(),k}`
generates a proper clock-invariant differential subfield of `C⟨y⟩` whose generator is a clock
eigenvector of character exactly `λ^k`.

Thus the quantized charge is not merely non-vacuous — it attains every value in `ℕ_{≥1}`, and each is
witnessed by an explicit charged core `C⟨y^(k)⟩`.  This generalizes the `k = 1` witness `C⟨y'⟩`.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [Field C]

/-- Iterated jets compose additively: `(y^(k))^(m) = y^(m+k)`. -/
theorem differentialJet_differentialJet (m k : ℕ) (x : ScalarDifferentialField C) :
    differentialJet m (differentialJet k x) = differentialJet (m + k) x := by
  simp only [differentialJet]
  rw [← Function.iterate_add_apply]

/-- **Proper subfield at charge `k`.**  For `k ≥ 1` the jet `y^(k)` differentially generates a subfield
omitting `y = X_{(),0}`, so `differentialAdjoin C {y^(k)} ≠ ⊤`. -/
theorem differentialAdjoin_differentialJet_ne_top (k : ℕ) (hk : 1 ≤ k) :
    differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)}
      ≠ (⊤ : IntermediateField C (ScalarDifferentialField C)) := by
  have hX : AlgebraicIndependent C
      (fun n : ℕ => (MvPolynomial.X ((), n) : DifferentialPolynomial Unit C)) :=
    (MvPolynomial.algebraicIndependent_X (Unit × ℕ) C).comp (fun n : ℕ => ((), n))
      (fun a b hab => by simpa using hab)
  have hinj : Function.Injective
      (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)) :=
    IsFractionRing.injective _ _
  have hmap : AlgebraicIndependent C
      (fun n : ℕ => algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
        (MvPolynomial.X ((), n))) :=
    hX.map (f := IsScalarTower.toAlgHom C (DifferentialPolynomial Unit C)
      (ScalarDifferentialField C)) hinj.injOn
  have hset : (fun n : ℕ => algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
        (MvPolynomial.X ((), n))) '' {n : ℕ | k ≤ n}
      = differentialJetSet {differentialJet k (scalarDifferentialGenerator C)} := by
    ext z
    simp only [differentialJetSet, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨differentialJet k (scalarDifferentialGenerator C), rfl, n - k, ?_⟩
      rw [differentialJet_differentialJet, Nat.sub_add_cancel hn,
        differentialJet_scalarDifferentialGenerator]
    · rintro ⟨w, rfl, m, rfl⟩
      exact ⟨m + k, Nat.le_add_left k m, by
        rw [differentialJet_differentialJet, differentialJet_scalarDifferentialGenerator]⟩
  have hi : (0 : ℕ) ∉ {n : ℕ | k ≤ n} := by simp only [Set.mem_setOf_eq]; omega
  have htr := hmap.transcendental_adjoin hi
  rw [hset] at htr
  have htrIF := IntermediateField.transcendental_adjoin_iff.mpr htr
  intro htop
  have hmem : ((fun n : ℕ => algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
        (MvPolynomial.X ((), n))) 0)
      ∈ differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)} := by
    rw [htop]; exact IntermediateField.mem_top
  exact htrIF (isAlgebraic_algebraMap
    (⟨_, hmem⟩ : IntermediateField.adjoin C
      (differentialJetSet {differentialJet k (scalarDifferentialGenerator C)})))

/-- **Clock-invariance at charge `k`.**  The clock maps `C⟨y^(k)⟩` into itself. -/
theorem clockDilationFieldEquiv_mem_differentialAdjoin_differentialJet
    (lam : C) (hlam : lam ≠ 0) (k : ℕ) {z : ScalarDifferentialField C}
    (hz : z ∈ differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)}) :
    clockDilationFieldEquiv lam hlam z
      ∈ differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)} := by
  have hle : differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)}
      ≤ (differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)}).comap
          (clockDilationFieldEquiv lam hlam).toAlgHom := by
    unfold differentialAdjoin
    rw [IntermediateField.adjoin_le_iff]
    intro s hs
    show clockDilationFieldEquiv lam hlam s
      ∈ IntermediateField.adjoin C
          (differentialJetSet {differentialJet k (scalarDifferentialGenerator C)})
    simp only [differentialJetSet, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs
    obtain ⟨w, rfl, m, hms⟩ := hs
    rw [← hms, differentialJet_differentialJet, clockDilationFieldEquiv_differentialJet]
    refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    rw [← differentialJet_differentialJet]
    exact IntermediateField.subset_adjoin _ _
      ⟨differentialJet k (scalarDifferentialGenerator C), rfl, m, rfl⟩
  exact hle hz

/-- **The clock charge realizes every positive value.**  For each `k ≥ 1`, the `k`-th jet `y^(k)`
generates a proper clock-invariant differential subfield of `C⟨y⟩` whose generator is a clock
eigenvector of character exactly `λ^k`.  Hence the quantized charge of the clock-character law attains
every positive integer, each witnessed by the explicit charged core `C⟨y^(k)⟩`. -/
theorem clock_charge_spectrum (k : ℕ) (hk : 1 ≤ k) :
    differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)}
        ≠ (⊤ : IntermediateField C (ScalarDifferentialField C))
      ∧ (∀ lam : C, (hlam : lam ≠ 0) →
          clockDilationFieldEquiv lam hlam (differentialJet k (scalarDifferentialGenerator C))
            = algebraMap C (ScalarDifferentialField C) (lam ^ k)
              * differentialJet k (scalarDifferentialGenerator C))
      ∧ (∀ lam : C, (hlam : lam ≠ 0) →
          ∀ z ∈ differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)},
            clockDilationFieldEquiv lam hlam z
              ∈ differentialAdjoin C {differentialJet k (scalarDifferentialGenerator C)}) :=
  ⟨differentialAdjoin_differentialJet_ne_top k hk,
   fun lam hlam => clockDilationFieldEquiv_differentialJet lam hlam k,
   fun lam hlam _z hz =>
     clockDilationFieldEquiv_mem_differentialAdjoin_differentialJet lam hlam k hz⟩

end

end GaloisForLFunctions
