import GaloisForLFunctions.HTGeometry.AffineBaseJetGauge

/-!
# A nonzero base gauge changes no finite jet field

For a differential field extension `F ⊆ L`, a nonzero `a ∈ F` and `x ∈ L`, Leibniz gives

```text
Dⁱ(a x) = ∑_{k ≤ i} c_{i,k} Dᵏ x,   c_{i,k} ∈ F,   c_{i,i} = a,
```

so the finite jet fields `F(x, Dx, …, Dᵐ x)` and `F(ax, D(ax), …, Dᵐ(ax))` coincide.  Applying the
same expansion one step further shows that the top jet is algebraic over the previous ones for
`a x` exactly when it is for `x`: the minimal differential aperture is a gauge invariant.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

variable {F L : Type*} [Field F] [Field L] [Algebra F L]
  [Differential F] [Differential L] [DifferentialAlgebra F L]

/-- **Leibniz expansion of a base gauge.**  Every jet of `a x` is an `F`-linear combination of the
jets of `x` of no larger order, with top coefficient `a`. -/
theorem exists_baseCombination_differentialJet_mul (a : F) (x : L) (i : ℕ) :
    ∃ c : ℕ → F, (∀ k, i < k → c k = 0) ∧ c i = a ∧
      differentialJet i (algebraMap F L a * x)
        = ∑ k ∈ Finset.range (i + 1), algebraMap F L (c k) * differentialJet k x := by
  classical
  induction i with
  | zero =>
      refine ⟨fun k => if k = 0 then a else 0, ?_, ?_, ?_⟩
      · intro k hk
        show (if k = 0 then a else 0) = 0
        rw [if_neg (by omega)]
      · show (if (0 : ℕ) = 0 then a else 0) = a
        rw [if_pos rfl]
      · simp
  | succ i ih =>
      obtain ⟨c, hsupp, htop, hrep⟩ := ih
      refine ⟨fun j => Differential.deriv (c j) + (if j = 0 then 0 else c (j - 1)), ?_, ?_, ?_⟩
      · intro k hk
        show Differential.deriv (c k) + (if k = 0 then 0 else c (k - 1)) = 0
        have h1 : c k = 0 := hsupp k (by omega)
        have h2 : (if k = 0 then (0 : F) else c (k - 1)) = 0 := by
          rcases Nat.eq_zero_or_pos k with h | h
          · rw [if_pos h]
          · rw [if_neg (by omega)]
            exact hsupp _ (by omega)
        rw [h1, h2, map_zero, add_zero]
      · show Differential.deriv (c (i + 1))
            + (if i + 1 = 0 then 0 else c (i + 1 - 1)) = a
        have h1 : c (i + 1) = 0 := hsupp _ (by omega)
        rw [h1, map_zero, if_neg (by omega), zero_add]
        simpa using htop
      · have hstep : ∀ k : ℕ,
            Differential.deriv (algebraMap F L (c k) * differentialJet k x)
              = algebraMap F L (Differential.deriv (c k)) * differentialJet k x
                + algebraMap F L (c k) * differentialJet (k + 1) x := by
          intro k
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, ← deriv_algebraMap,
            differentialJet_succ]
          ring
        rw [differentialJet_succ, hrep, map_sum,
          Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range (i + 1)) => hstep k),
          Finset.sum_add_distrib]
        have hRHS : (∑ j ∈ Finset.range (i + 2),
            algebraMap F L (Differential.deriv (c j) + (if j = 0 then 0 else c (j - 1)))
              * differentialJet j x)
            = (∑ j ∈ Finset.range (i + 2),
                algebraMap F L (Differential.deriv (c j)) * differentialJet j x)
              + ∑ j ∈ Finset.range (i + 2),
                algebraMap F L (if j = 0 then 0 else c (j - 1)) * differentialJet j x := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by rw [map_add]; ring
        rw [hRHS]
        congr 1
        · symm
          rw [Finset.sum_range_succ]
          have h1 : c (i + 1) = 0 := hsupp _ (by omega)
          rw [h1, map_zero, map_zero, zero_mul, add_zero]
        · symm
          rw [Finset.sum_range_succ' (fun j => algebraMap F L
            (if j = 0 then (0 : F) else c (j - 1)) * differentialJet j x) (i + 1)]
          rw [if_pos rfl, map_zero, zero_mul, add_zero]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [if_neg (Nat.succ_ne_zero k)]
          norm_num

/-- The finite jet field of an element over the differential base. -/
def jetField (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L] [Differential L]
    (x : L) (m : ℕ) : IntermediateField F L :=
  IntermediateField.adjoin F ((fun k => differentialJet k x) '' Set.Iic m)

omit [Differential F] [DifferentialAlgebra F L] in
theorem differentialJet_mem_jetField (x : L) {m k : ℕ} (hk : k ≤ m) :
    differentialJet k x ∈ jetField F x m :=
  IntermediateField.subset_adjoin F _ ⟨k, hk, rfl⟩

theorem differentialJet_mul_base_mem_jetField (a : F) (x : L) {m i : ℕ} (hi : i ≤ m) :
    differentialJet i (algebraMap F L a * x) ∈ jetField F x m := by
  obtain ⟨c, -, -, hrep⟩ := exists_baseCombination_differentialJet_mul a x i
  rw [hrep]
  refine Subalgebra.sum_mem _ fun k hk => ?_
  refine Subalgebra.mul_mem _ ?_ ?_
  · exact (jetField F x m).algebraMap_mem _
  · exact differentialJet_mem_jetField x (le_trans (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk)) hi)

theorem jetField_mul_base_le (a : F) (x : L) (m : ℕ) :
    jetField F (algebraMap F L a * x) m ≤ jetField F x m := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro - ⟨i, hi, rfl⟩
  exact differentialJet_mul_base_mem_jetField a x hi

/-- **A nonzero base gauge leaves every finite jet field unchanged.**  This is equation `(3a)` of
the gauge-blindness card at the level of jet fields. -/
theorem jetField_mul_base_eq {a : F} (ha : a ≠ 0) (x : L) (m : ℕ) :
    jetField F (algebraMap F L a * x) m = jetField F x m := by
  refine le_antisymm (jetField_mul_base_le a x m) ?_
  have hback : jetField F (algebraMap F L a⁻¹ * (algebraMap F L a * x)) m
      ≤ jetField F (algebraMap F L a * x) m :=
    jetField_mul_base_le a⁻¹ _ m
  have hx : algebraMap F L a⁻¹ * (algebraMap F L a * x) = x := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  rwa [hx] at hback

/-! ## Aperture invariance -/

/-- The aperture predicate at level `m`: the fresh jet is algebraic over the jet prefix field. -/
def JetAlgebraicOver (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L] [Differential L]
    (x : L) (m : ℕ) : Prop :=
  IsAlgebraic (jetField F x m) (differentialJet (m + 1) x)

omit [Differential F] [DifferentialAlgebra F L] in
theorem isAlgebraic_of_mem_jetField {x v : L} {m : ℕ} (hv : v ∈ jetField F x m) :
    IsAlgebraic (jetField F x m) v := by
  have h := isAlgebraic_algebraMap (R := jetField F x m) (A := L) (⟨v, hv⟩ : jetField F x m)
  simpa using h

/-- **The minimal differential aperture is a base-gauge invariant.**  Equation `(3a)`. -/
theorem jetAlgebraicOver_mul_base_iff {a : F} (ha : a ≠ 0) (x : L) (m : ℕ) :
    JetAlgebraicOver F (algebraMap F L a * x) m ↔ JetAlgebraicOver F x m := by
  classical
  obtain ⟨c, -, htop, hrep⟩ := exists_baseCombination_differentialJet_mul a x (m + 1)
  have hJeq : jetField F (algebraMap F L a * x) m = jetField F x m :=
    jetField_mul_base_eq ha x m
  set w : L := ∑ k ∈ Finset.range (m + 1), algebraMap F L (c k) * differentialJet k x with hw
  have hwmem : w ∈ jetField F x m := by
    refine Subalgebra.sum_mem _ fun k hk => ?_
    exact Subalgebra.mul_mem _ ((jetField F x m).algebraMap_mem _)
      (differentialJet_mem_jetField x (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hsplit : differentialJet (m + 1) (algebraMap F L a * x)
      = algebraMap F L a * differentialJet (m + 1) x + w := by
    rw [hrep, Finset.sum_range_succ, htop, hw]
    ring
  have hane : algebraMap F L a ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap F L) (algebraMap F L).injective).mpr ha
  have hamem : algebraMap F L a ∈ jetField F x m := (jetField F x m).algebraMap_mem a
  have haInvMem : (algebraMap F L a)⁻¹ ∈ jetField F x m := (jetField F x m).inv_mem hamem
  rw [JetAlgebraicOver, JetAlgebraicOver, hJeq, hsplit]
  constructor
  · intro h
    have hsub : IsAlgebraic (jetField F x m) (algebraMap F L a * differentialJet (m + 1) x) := by
      have := h.sub (isAlgebraic_of_mem_jetField hwmem)
      simpa using this
    have hmul := (isAlgebraic_of_mem_jetField haInvMem).mul hsub
    have hval : (algebraMap F L a)⁻¹ * (algebraMap F L a * differentialJet (m + 1) x)
        = differentialJet (m + 1) x := by
      rw [← mul_assoc, inv_mul_cancel₀ hane, one_mul]
    rwa [hval] at hmul
  · intro h
    exact ((isAlgebraic_of_mem_jetField hamem).mul h).add (isAlgebraic_of_mem_jetField hwmem)


end

end GaloisForLFunctions.HTGeometry
