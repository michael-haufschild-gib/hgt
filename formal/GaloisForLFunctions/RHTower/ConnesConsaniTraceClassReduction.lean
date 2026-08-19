import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.RHTower.TraceNorm
import GaloisForLFunctions.RHTower.SchattenApproximation
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.RHTower.DeningerNuclearSchattenBridge
import GaloisForLFunctions.HTGeometry.RankOneHilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

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
theorem memSchattenClass_one_modulusSq_sub_of_adjoint {E R : H →L[ℂ] H}
    (hR1 : MemSchattenClass 1 R)
    (hRa1 : MemSchattenClass 1 (ContinuousLinearMap.adjoint R)) :
    MemSchattenClass 1
      (ContinuousLinearMap.adjoint (E + R) ∘L (E + R)
        - ContinuousLinearMap.adjoint E ∘L E) := by
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

/-- **A trace-class perturbation perturbs the modulus square by a trace-class operator.** -/
theorem memSchattenClass_one_modulusSq_sub {E R : H →L[ℂ] H} (hR : IsTraceClass R) :
    MemSchattenClass 1
      (ContinuousLinearMap.adjoint (E + R) ∘L (E + R)
        - ContinuousLinearMap.adjoint E ∘L E) :=
  memSchattenClass_one_modulusSq_sub_of_adjoint (IsTraceClass.memSchattenClass_one hR)
    (IsTraceClass.memSchattenClass_one (IsTraceClass.adjoint hR))

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

/-- **A finite-rank operator is Hilbert--Schmidt.**  Expanding the image in an orthonormal basis of
the finite-dimensional range subspace writes the operator as a finite sum of rank-one operators. -/
theorem isHilbertSchmidt_of_hasRankLE {F : H →L[ℂ] H} {n : ℕ} (hF : HasRankLE F n) :
    IsHilbertSchmidt F := by
  classical
  obtain ⟨V, hVfin, hVrank, hVmem⟩ := hF
  haveI : FiniteDimensional ℂ V := hVfin
  set b := stdOrthonormalBasis ℂ V with hb
  have hexp : F = ∑ j, ((innerSL ℂ ((b j : V) : H)).comp F).smulRight ((b j : V) : H) := by
    ext x
    have hy : ∑ j, b.repr ⟨F x, hVmem x⟩ j • b j = (⟨F x, hVmem x⟩ : V) := b.sum_repr _
    have hcoe : ((∑ j, b.repr ⟨F x, hVmem x⟩ j • b j : V) : H) = F x := by
      rw [hy]
    rw [sum_apply]
    rw [← hcoe, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply]
    congr 1
    rw [OrthonormalBasis.repr_apply_apply]
    rfl
  rw [hexp]
  refine Finset.sum_induction _ ContinuousLinearMap.IsHilbertSchmidt
    (fun a c ha hc => ha.add hc) isHilbertSchmidt_zero ?_
  intro j _
  exact GaloisForLFunctions.HTGeometry.isHilbertSchmidt_smulRight _ _

/-- **A finite-rank operator is trace class** in the factorization sense: it factors through the
orthogonal projection onto its finite-dimensional range subspace, and both factors are
Hilbert--Schmidt. -/
theorem isTraceClass_of_hasRankLE {F : H →L[ℂ] H} {n : ℕ} (hF : HasRankLE F n) :
    IsTraceClass F := by
  classical
  obtain ⟨V, hVfin, hVrank, hVmem⟩ := hF
  haveI : FiniteDimensional ℂ V := hVfin
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  set Q : H →L[ℂ] H := V.starProjection with hQ
  have hQrank : HasRankLE Q n :=
    ⟨V, hVfin, hVrank, fun x => V.starProjection_apply_mem x⟩
  have hQF : Q ∘L F = F := by
    ext x
    show V.starProjection (F x) = F x
    rw [Submodule.starProjection_eq_self_iff.mpr (hVmem x)]
  exact ⟨Q, F, isHilbertSchmidt_of_hasRankLE hQrank,
    isHilbertSchmidt_of_hasRankLE ⟨V, hVfin, hVrank, hVmem⟩, hQF.symm⟩

/-- **The source reduction with a finite-rank remainder.**  This discharges the finite-rank
disjunct of the Connes--Consani premise: no trace-class hypothesis is assumed, only that the omitted
terms have finite rank. -/
theorem memSchattenClass_one_modulusPow_sub_of_hasRankLE {E R : H →L[ℂ] H} {n : ℕ}
    (hR : HasRankLE R n) (m : ℕ) :
    MemSchattenClass 1
      ((ContinuousLinearMap.adjoint (E + R) ∘L (E + R)) ^ m
        - (ContinuousLinearMap.adjoint E ∘L E) ^ m) :=
  memSchattenClass_one_modulusPow_sub (isTraceClass_of_hasRankLE hR) m

/-- **The power reduction from Schatten-1 data on the remainder and its adjoint.** -/
theorem memSchattenClass_one_modulusPow_sub_of_adjoint {E R : H →L[ℂ] H}
    (hR1 : MemSchattenClass 1 R)
    (hRa1 : MemSchattenClass 1 (ContinuousLinearMap.adjoint R)) (m : ℕ) :
    MemSchattenClass 1
      ((ContinuousLinearMap.adjoint (E + R) ∘L (E + R)) ^ m
        - (ContinuousLinearMap.adjoint E ∘L E) ^ m) := by
  have hdiff := memSchattenClass_one_modulusSq_sub_of_adjoint (E := E) hR1 hRa1
  have hsplit : ContinuousLinearMap.adjoint (E + R) ∘L (E + R)
      = ContinuousLinearMap.adjoint E ∘L E
        + (ContinuousLinearMap.adjoint (E + R) ∘L (E + R)
          - ContinuousLinearMap.adjoint E ∘L E) := by
    abel
  rw [hsplit]
  exact memSchattenClass_one_pow_sub hdiff m

/-- **The adjoint of a rank-one operator is rank one**, with the roles of the functional and the
vector exchanged through the Riesz representation. -/
theorem adjoint_smulRight (φ : H →L[ℂ] ℂ) (y : H) :
    ContinuousLinearMap.adjoint (φ.smulRight y)
      = (innerSL ℂ y).smulRight ((InnerProductSpace.toDual ℂ H).symm φ) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z x
  have hu : ∀ w : H, inner ℂ ((InnerProductSpace.toDual ℂ H).symm φ) w = φ w := by
    intro w
    rw [InnerProductSpace.toDual_symm_apply]
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    inner_smul_left, inner_smul_right, hu x]
  simp [inner_conj_symm, mul_comm]

/-- The adjoint of an absolutely norm-summable rank-one series is the series of the adjoints. -/
theorem adjoint_tsum_smulRight {ι : Type*} (φ : ι → H →L[ℂ] ℂ) (y : ι → H)
    (hnorm : Summable fun k => ‖(φ k).smulRight (y k)‖) :
    ContinuousLinearMap.adjoint (∑' k, (φ k).smulRight (y k))
      = ∑' k, ContinuousLinearMap.adjoint ((φ k).smulRight (y k)) := by
  have hsum : Summable fun k => (φ k).smulRight (y k) := Summable.of_norm hnorm
  have hmap := hsum.hasSum.map
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := H) (F := H)).toLinearEquiv.toAddEquiv.toAddMonoidHom
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := H) (F := H)).continuous
  exact (hmap.tsum_eq).symm

/-- **The source reduction with a nuclear remainder.**  This discharges the smoothing disjunct of
the Connes--Consani premise: the omitted terms are given as an absolutely norm-summable series of
rank-one operators, and no trace-class hypothesis is assumed. -/
theorem memSchattenClass_one_modulusPow_sub_of_nuclear {E : H →L[ℂ] H} {ι : Type*}
    (φ : ι → H →L[ℂ] ℂ) (y : ι → H)
    (hnorm : Summable fun k => ‖(φ k).smulRight (y k)‖) (m : ℕ) :
    MemSchattenClass 1
      ((ContinuousLinearMap.adjoint (E + ∑' k, (φ k).smulRight (y k))
          ∘L (E + ∑' k, (φ k).smulRight (y k))) ^ m
        - (ContinuousLinearMap.adjoint E ∘L E) ^ m) := by
  classical
  have hrank : ∀ k, HasRankLE ((φ k).smulRight (y k)) 1 := fun k =>
    deningerSmulRight_hasRankLE_one (φ k) (y k)
  have hR1 : MemSchattenClass 1 (∑' k, (φ k).smulRight (y k)) :=
    memSchattenClass_one_tsum_rankOneTerms_of_summable_norm _ hrank hnorm
  -- the adjoint series
  have hadj : ∀ k, ContinuousLinearMap.adjoint ((φ k).smulRight (y k))
      = (innerSL ℂ (y k)).smulRight ((InnerProductSpace.toDual ℂ H).symm (φ k)) := fun k =>
    adjoint_smulRight (φ k) (y k)
  have hnormadj : Summable fun k =>
      ‖(innerSL ℂ (y k)).smulRight ((InnerProductSpace.toDual ℂ H).symm (φ k))‖ := by
    refine hnorm.congr fun k => ?_
    rw [← hadj k]
    exact ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := H) (F := H)).norm_map _).symm
  have hrankadj : ∀ k,
      HasRankLE ((innerSL ℂ (y k)).smulRight ((InnerProductSpace.toDual ℂ H).symm (φ k))) 1 :=
    fun k => deningerSmulRight_hasRankLE_one _ _
  have hRa1 : MemSchattenClass 1
      (ContinuousLinearMap.adjoint (∑' k, (φ k).smulRight (y k))) := by
    rw [adjoint_tsum_smulRight φ y hnorm]
    simp only [hadj]
    exact memSchattenClass_one_tsum_rankOneTerms_of_summable_norm _ hrankadj hnormadj
  exact memSchattenClass_one_modulusPow_sub_of_adjoint hR1 hRa1 m

end

end RHTower
