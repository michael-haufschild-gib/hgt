import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.RHTower.TraceNorm
import GaloisForLFunctions.RHTower.SchattenApproximation

/-!
# The one-prime source reduction, as a trace-class perturbation law

Connes--Consani's one-prime decomposition writes the Hankel operator as a distinguished block plus
terms that are rapidly smoothing or finite rank, and concludes that the `2m`-th positive powers of
the two differ by a trace-class operator.

The content of that conclusion is a general perturbation law, proved here unconditionally: the
Schatten 1-class is a two-sided ideal closed under addition, so a trace-class perturbation of an
operator perturbs its modulus square, and hence every power of the modulus square, by a trace-class
operator.
-/

open ContinuousLinearMap

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trace class is closed under adjoints: a Hilbert--Schmidt factorization transposes. -/
theorem IsTraceClass.adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (ContinuousLinearMap.adjoint T) := by
  obtain ⟨S, U, hS, hU, hTSU⟩ := hT
  refine ⟨ContinuousLinearMap.adjoint U, ContinuousLinearMap.adjoint S, hU.adjoint, hS.adjoint, ?_⟩
  rw [hTSU, ContinuousLinearMap.adjoint_comp]

/-- **A trace-class perturbation perturbs the modulus square by a trace-class operator.** -/
theorem memSchattenClass_one_modulusSq_sub {E R : H →L[ℂ] H} (hR : IsTraceClass R) :
    MemSchattenClass 1
      (ContinuousLinearMap.adjoint (E + R) ∘L (E + R)
        - ContinuousLinearMap.adjoint E ∘L E) := by
  have hR1 : MemSchattenClass 1 R := IsTraceClass.memSchattenClass_one hR
  have hRa1 : MemSchattenClass 1 (ContinuousLinearMap.adjoint R) :=
    IsTraceClass.memSchattenClass_one (IsTraceClass.adjoint hR)
  have hid : ContinuousLinearMap.adjoint (E + R) ∘L (E + R)
      - ContinuousLinearMap.adjoint E ∘L E
      = ContinuousLinearMap.adjoint E ∘L R
        + (ContinuousLinearMap.adjoint R ∘L E + ContinuousLinearMap.adjoint R ∘L R) := by
    rw [map_add]
    simp only [← ContinuousLinearMap.mul_def]
    noncomm_ring
  rw [hid]
  exact (memSchattenClass_one_comp_left hR1 _).one_add
    ((memSchattenClass_one_comp_right hRa1 _).one_add
      (memSchattenClass_one_comp_right hRa1 _))

/-- **A trace-class perturbation propagates to every power.** -/
theorem memSchattenClass_one_pow_sub {A T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) :
    ∀ m : ℕ, MemSchattenClass 1 ((A + T) ^ m - A ^ m) := by
  intro m
  induction m with
  | zero => simpa using memSchattenClass_one_smul hT 0
  | succ m ih =>
      have hid : (A + T) ^ (m + 1) - A ^ (m + 1)
          = ((A + T) ^ m - A ^ m) ∘L (A + T) + (A ^ m) ∘L T := by
        rw [pow_succ, pow_succ]
        simp only [← ContinuousLinearMap.mul_def]
        noncomm_ring
      rw [hid]
      exact (memSchattenClass_one_comp_right ih (A + T)).one_add
        (memSchattenClass_one_comp_left hT (A ^ m))

/-- **The Connes--Consani one-prime source reduction.**  If the omitted terms of the decomposition
are trace class, then the `2m`-th positive powers of the full operator and of its distinguished
block differ by a trace-class operator. -/
theorem memSchattenClass_one_modulusPow_sub {E R : H →L[ℂ] H} (hR : IsTraceClass R) (m : ℕ) :
    MemSchattenClass 1
      ((ContinuousLinearMap.adjoint (E + R) ∘L (E + R)) ^ m
        - (ContinuousLinearMap.adjoint E ∘L E) ^ m) := by
  have hdiff := memSchattenClass_one_modulusSq_sub (E := E) hR
  have hsplit : ContinuousLinearMap.adjoint (E + R) ∘L (E + R)
      = ContinuousLinearMap.adjoint E ∘L E
        + (ContinuousLinearMap.adjoint (E + R) ∘L (E + R)
          - ContinuousLinearMap.adjoint E ∘L E) := by
    abel
  rw [hsplit]
  exact memSchattenClass_one_pow_sub hdiff m

omit [CompleteSpace H] in
/-- **A finite-rank operator is trace class.**  Its approximation numbers vanish from the rank on,
so the Schatten-1 series is a finite sum. -/
theorem memSchattenClass_one_of_hasRankLE {F : H →L[ℂ] H} {n : ℕ} (hF : HasRankLE F n) :
    MemSchattenClass 1 F := by
  classical
  have hzero : ∀ k : ℕ, n ≤ k → approxNumber F k = 0 := by
    intro k hk
    refine le_antisymm ?_ (approxNumber_nonneg F k)
    have hle := approxNumber_le F k F (hF.mono hk)
    simpa using hle
  refine summable_of_ne_finset_zero (s := Finset.range n) ?_
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  rw [hzero k hk]
  simp

/-- **The source reduction with the remainder in Hilbert--Schmidt factorized form.**  This is the
shape in which a smoothing remainder is normally presented, and it needs no separate adjoint-closure
argument: the factorization transposes. -/
theorem memSchattenClass_one_modulusPow_sub_of_hilbertSchmidt {E S U : H →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hU : IsHilbertSchmidt U) (m : ℕ) :
    MemSchattenClass 1
      ((ContinuousLinearMap.adjoint (E + S ∘L U) ∘L (E + S ∘L U)) ^ m
        - (ContinuousLinearMap.adjoint E ∘L E) ^ m) :=
  memSchattenClass_one_modulusPow_sub (hS.comp_isTraceClass hU) m

end

end RHTower
