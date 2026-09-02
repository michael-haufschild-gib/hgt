import GaloisForLFunctions.HTGeometry.DifferentialVariationalLatticeCommensurability

/-!
# Rank-one differential variational building

A finitely generated full valuation lattice in one completed pseudodifferential coordinate is
principal.  Choosing a generator of least finite additive valuation makes every other generator an
integral left multiple.  Inner-conjugation invariance of the valuation ring then identifies this
principal left module with a correctly oriented left homothety of the standard lattice.

Thus the entire projective rank-one carrier, not only its standard apartment, has one point.  This
is the exact type-`A₀` geometric half of the rank-one no-displacement law.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

private noncomputable def rankOneFiniteAddValue
    (x : Fin 1 → CompletedPseudoDiffOp K) : ℤ := by
  classical
  exact if hx : x 0 = 0 then 0 else
    completedPseudoDiffOpUnitAddValue (Units.mk0 (x 0) hx)

private theorem rankOneFiniteAddValue_eq
    {x : Fin 1 → CompletedPseudoDiffOp K} (hx : x 0 ≠ 0) :
    rankOneFiniteAddValue x =
      completedPseudoDiffOpUnitAddValue (Units.mk0 (x 0) hx) := by
  simp [rankOneFiniteAddValue, hx]

private theorem rankOne_vector_ne_zero_iff
    (x : Fin 1 → CompletedPseudoDiffOp K) : x ≠ 0 ↔ x 0 ≠ 0 := by
  constructor
  · intro hx hx0
    apply hx
    funext i
    fin_cases i
    exact hx0
  · intro hx0 hx
    exact hx0 (congrFun hx 0)

private theorem rankOne_carrier_ne_bot
    (L : CompletedPseudoDiffOpLattice K (Fin 1)) : L.carrier ≠ ⊥ := by
  intro hbot
  have hfull := L.full
  rw [hbot] at hfull
  have hzero : Submodule.span (CompletedPseudoDiffOp K)
      ((⊥ : Submodule (CompletedPseudoDiffOpInteger (K := K))
        (Fin 1 → CompletedPseudoDiffOp K)) : Set (Fin 1 → CompletedPseudoDiffOp K)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    intro x hx
    simpa using hx
  rw [hzero] at hfull
  exact (show (⊥ : Submodule (CompletedPseudoDiffOp K)
    (Fin 1 → CompletedPseudoDiffOp K)) ≠ ⊤ by exact bot_ne_top) hfull

/-- Every rank-one full finite valuation lattice is principal over the valuation ring. -/
theorem exists_generator_rankOne_completedPseudoDiffOpLattice
    (L : CompletedPseudoDiffOpLattice K (Fin 1)) :
    ∃ s : Fin 1 → CompletedPseudoDiffOp K, s 0 ≠ 0 ∧
      L.carrier = (CompletedPseudoDiffOpInteger (K := K)) ∙ s := by
  classical
  obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp L.fg
  have hSnonzero : ∃ s ∈ S, s 0 ≠ 0 := by
    by_contra h
    push Not at h
    have hspanbot : Submodule.span (CompletedPseudoDiffOpInteger (K := K)) S = ⊥ := by
      rw [Submodule.span_eq_bot]
      intro s hs
      funext i
      fin_cases i
      exact h s hs
    apply rankOne_carrier_ne_bot L
    rw [← hSspan, hspanbot]
  let Snonzero : Finset (Fin 1 → CompletedPseudoDiffOp K) :=
    hSfinite.toFinset.filter (fun s => s 0 ≠ 0)
  have hSnonzero' : Snonzero.Nonempty := by
    obtain ⟨s, hsS, hs0⟩ := hSnonzero
    exact ⟨s, by simp [Snonzero, hSfinite.mem_toFinset, hsS, hs0]⟩
  obtain ⟨s, hs, hmin⟩ := Snonzero.exists_min_image rankOneFiniteAddValue hSnonzero'
  have hsS : s ∈ S := by
    exact (Finset.mem_filter.mp hs).1 |> hSfinite.mem_toFinset.mp
  have hs0 : s 0 ≠ 0 := by
    exact (Finset.mem_filter.mp hs).2
  refine ⟨s, hs0, ?_⟩
  rw [← hSspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    intro t ht
    by_cases ht0 : t 0 = 0
    · have htzero : t = 0 := by
        funext i
        fin_cases i
        exact ht0
      subst t
      exact Submodule.zero_mem _
    · let sUnit : (CompletedPseudoDiffOp K)ˣ := Units.mk0 (s 0) hs0
      let tUnit : (CompletedPseudoDiffOp K)ˣ := Units.mk0 (t 0) ht0
      have htmem : t ∈ Snonzero := by
        simp [Snonzero, hSfinite.mem_toFinset, ht, ht0]
      have hval : completedPseudoDiffOpUnitAddValue sUnit ≤
          completedPseudoDiffOpUnitAddValue tUnit := by
        have h := hmin t htmem
        simpa [rankOneFiniteAddValue_eq hs0,
          rankOneFiniteAddValue_eq ht0, sUnit, tUnit] using h
      have hratio : t 0 * (sUnit⁻¹ : CompletedPseudoDiffOp K) ∈
          CompletedPseudoDiffOpInteger (K := K) := by
        rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg]
        change 0 ≤ completedPseudoDiffOpAddValue
          (((tUnit * sUnit⁻¹ : (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K))
        rw [completedPseudoDiffOpAddValue_unit_eq_coe,
          completedPseudoDiffOpUnitAddValue_mul,
          completedPseudoDiffOpUnitAddValue_inv]
        norm_cast
        omega
      apply Submodule.mem_span_singleton.mpr
      refine ⟨⟨t 0 * (sUnit⁻¹ : CompletedPseudoDiffOp K), hratio⟩, ?_⟩
      funext i
      fin_cases i
      change (t 0 * (sUnit⁻¹ : CompletedPseudoDiffOp K)) * s 0 = t 0
      rw [mul_assoc, show (sUnit⁻¹ : CompletedPseudoDiffOp K) = (s 0)⁻¹ by rfl,
        inv_mul_cancel₀ hs0, mul_one]
  · apply Submodule.span_mono
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rwa [ht]

/-- Every rank-one full finite valuation lattice is left-homothetic to the standard lattice. -/
theorem standardCompletedPseudoDiffOpLattice_leftHomothetic_rankOne
    (L : CompletedPseudoDiffOpLattice K (Fin 1)) :
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin 1)).LeftHomothetic L := by
  classical
  obtain ⟨s, hs0, hL⟩ := exists_generator_rankOne_completedPseudoDiffOpLattice L
  let a : (CompletedPseudoDiffOp K)ˣ := Units.mk0 (s 0) hs0
  refine ⟨a, CompletedPseudoDiffOpLattice.ext ?_⟩
  rw [hL]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ :=
      (mem_leftScaleCompletedPseudoDiffOpLattice_iff a
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin 1)) y).1 hy
    have hx0 : x 0 ∈ CompletedPseudoDiffOpInteger (K := K) :=
      (mem_standardCompletedPseudoDiffOpLattice_iff x).1 hx 0
    apply Submodule.mem_span_singleton.mpr
    let c : CompletedPseudoDiffOpInteger (K := K) :=
      innerCompletedPseudoDiffOpIntegerEquiv a ⟨x 0, hx0⟩
    refine ⟨c, ?_⟩
    rw [← hxy]
    funext i
    fin_cases i
    change ((s 0 * x 0) * (s 0)⁻¹) * s 0 = s 0 * x 0
    rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  · intro hy
    obtain ⟨c, hcy⟩ := Submodule.mem_span_singleton.mp hy
    let d : CompletedPseudoDiffOpInteger (K := K) :=
      innerCompletedPseudoDiffOpIntegerEquiv a⁻¹ c
    let x : Fin 1 → CompletedPseudoDiffOp K := fun _ => d
    apply (mem_leftScaleCompletedPseudoDiffOpLattice_iff a
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin 1)) y).2
    refine ⟨x, ?_, ?_⟩
    · apply (mem_standardCompletedPseudoDiffOpLattice_iff x).2
      intro i
      exact d.property
    · rw [← hcy]
      funext i
      fin_cases i
      change s 0 * ((s 0)⁻¹ * (c : CompletedPseudoDiffOp K) * s 0) =
        (c : CompletedPseudoDiffOp K) * s 0
      calc
        s 0 * ((s 0)⁻¹ * (c : CompletedPseudoDiffOp K) * s 0) =
            ((s 0 * (s 0)⁻¹) * (c : CompletedPseudoDiffOp K)) * s 0 := by
          simp only [mul_assoc]
        _ = (c : CompletedPseudoDiffOp K) * s 0 := by
          rw [mul_inv_cancel₀ hs0, one_mul]

/-- The correctly oriented projective rank-one lattice carrier has exactly one point. -/
instance differentialVariationalProjectiveBuildingCarrierFinOne_subsingleton :
    Subsingleton (DifferentialVariationalProjectiveBuildingCarrier K (Fin 1)) where
  allEq x y := by
    induction x using Quotient.inductionOn with
    | _ L =>
        induction y using Quotient.inductionOn with
        | _ M =>
            apply Quotient.sound
            exact (standardCompletedPseudoDiffOpLattice_leftHomothetic_rankOne L).symm.trans
              (standardCompletedPseudoDiffOpLattice_leftHomothetic_rankOne M)

end

end GaloisForLFunctions.HTGeometry.DiffOp
