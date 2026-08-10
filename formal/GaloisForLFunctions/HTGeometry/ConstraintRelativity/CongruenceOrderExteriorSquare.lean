import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.GorensteinResidualFibre

/-!
# The diagonal congruence order and its exterior-square cotangent sector

Fix a commutative ring `R`, an element `a`, and `N = m + 1` sheets.  The *diagonal congruence
order* inside `O = R^N` is

`A = R·1 + a·O = {v : all coordinates congruent modulo a}`.

This file develops `A`: the observer defect `O/A ≅ k^m`, the finite presentation
`A ≅ R[x₁,…,x_m]/(xᵢ² − a xᵢ, xᵢxⱼ)`, and the resulting free `R`-basis `1, x₁, …, x_m`.
-/

namespace HTGeometry.ConstraintRelativity

open MvPolynomial

/-! ## The order and its observer defect -/

section Order

variable {R : Type*} [CommRing R] (a : R) (N : ℕ)

/-- The diagonal congruence order `R·1 + a·O` inside `O = R^N`, described as the set of vectors
all of whose coordinates agree modulo `a`. -/
def congruenceOrder : Subalgebra R (Fin N → R) where
  carrier := {v | ∀ i j, a ∣ v i - v j}
  mul_mem' := by
    intro v w hv hw i j
    show a ∣ v i * w i - v j * w j
    have h : v i * w i - v j * w j = v i * (w i - w j) + w j * (v i - v j) := by ring
    rw [h]
    exact dvd_add (Dvd.dvd.mul_left (hw i j) _) (Dvd.dvd.mul_left (hv i j) _)
  add_mem' := by
    intro v w hv hw i j
    show a ∣ v i + w i - (v j + w j)
    have h : v i + w i - (v j + w j) = (v i - v j) + (w i - w j) := by ring
    rw [h]
    exact dvd_add (hv i j) (hw i j)
  algebraMap_mem' := by
    intro r i j
    simp
theorem mem_congruenceOrder {v : Fin N → R} :
    v ∈ congruenceOrder a N ↔ ∀ i j, a ∣ v i - v j := Iff.rfl

variable {N}

/-- The observer projection `O → k^m`, `v ↦ (v i − v last)`. -/
def observerProj (m : ℕ) : (Fin (m + 1) → R) →ₗ[R] (Fin m → R ⧸ Ideal.span ({a} : Set R)) where
  toFun v i := Ideal.Quotient.mk _ (v i.castSucc - v (Fin.last m))
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    rw [← map_add]
    congr 1
    ring
  map_smul' r v := by
    funext i
    show Ideal.Quotient.mk _ (r * v i.castSucc - r * v (Fin.last m))
      = r • Ideal.Quotient.mk _ (v i.castSucc - v (Fin.last m))
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
    congr 1
    ring

theorem observerProj_apply (m : ℕ) (v : Fin (m + 1) → R) (i : Fin m) :
    observerProj a m v i = Ideal.Quotient.mk _ (v i.castSucc - v (Fin.last m)) := rfl

theorem observerProj_surjective (m : ℕ) : Function.Surjective (observerProj a m) := by
  intro w
  choose c hc using fun i => Ideal.Quotient.mk_surjective (I := Ideal.span ({a} : Set R)) (w i)
  refine ⟨Fin.snoc c 0, ?_⟩
  funext i
  rw [observerProj_apply]
  simp [hc i]

theorem ker_observerProj (m : ℕ) :
    LinearMap.ker (observerProj a m)
      = Subalgebra.toSubmodule (congruenceOrder a (m + 1)) := by
  ext v
  simp only [LinearMap.mem_ker, Subalgebra.mem_toSubmodule, mem_congruenceOrder]
  constructor
  · intro h i j
    have hi : a ∣ v i - v (Fin.last m) := by
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · have hcf := congrFun h i'
        rw [observerProj_apply] at hcf
        simp only [Pi.zero_apply] at hcf
        rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hcf
        exact hcf
      · simp
    have hj : a ∣ v j - v (Fin.last m) := by
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hcf := congrFun h j'
        rw [observerProj_apply] at hcf
        simp only [Pi.zero_apply] at hcf
        rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hcf
        exact hcf
      · simp
    have hd : v i - v j = (v i - v (Fin.last m)) - (v j - v (Fin.last m)) := by ring
    rw [hd]
    exact dvd_sub hi hj
  · intro h
    funext i
    rw [observerProj_apply]
    simp only [Pi.zero_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact h _ _

/-- **Card `(3)`.**  The observer defect of the diagonal congruence order is the `A_{N−1}` root
space: `O/A ≅ k^{N−1}`. -/
noncomputable def observerDefectEquiv (m : ℕ) :
    ((Fin (m + 1) → R) ⧸ Subalgebra.toSubmodule (congruenceOrder a (m + 1)))
      ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ (ker_observerProj a m).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (observerProj_surjective a m))

end Order

/-! ## The finite presentation -/

section Presentation

variable {R : Type*} [CommRing R] (a : R) (m : ℕ)

/-- The `i`-th source generator `xᵢ = a·eᵢ` of the congruence order. -/
def congruenceGen (i : Fin m) : Fin (m + 1) → R := a • Pi.single i.castSucc 1

/-- Evaluation of the polynomial ring at the source generators. -/
noncomputable def congruenceEval : MvPolynomial (Fin m) R →ₐ[R] (Fin (m + 1) → R) :=
  aeval (congruenceGen a m)

/-- The defining relations: each generator is idempotent up to `a`, and distinct generators
annihilate one another. -/
noncomputable def congruenceRelations : Set (MvPolynomial (Fin m) R) :=
  {f | (∃ i : Fin m, f = X i ^ 2 - C a * X i) ∨ ∃ i j : Fin m, i ≠ j ∧ f = X i * X j}

/-- The relation ideal of the congruence order. -/
noncomputable def congruenceIdeal : Ideal (MvPolynomial (Fin m) R) := Ideal.span (congruenceRelations a m)

variable {a m}

theorem congruenceGen_mul_self (i : Fin m) :
    congruenceGen a m i * congruenceGen a m i = a • congruenceGen a m i := by
  funext j
  simp only [congruenceGen, Pi.smul_apply, Pi.mul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem congruenceGen_mul_of_ne {i j : Fin m} (hij : i ≠ j) :
    congruenceGen a m i * congruenceGen a m j = 0 := by
  funext l
  simp only [congruenceGen, Pi.smul_apply, Pi.mul_apply, Pi.single_apply, Pi.zero_apply,
    smul_eq_mul]
  by_cases h1 : l = i.castSucc
  · have h2 : ¬ l = j.castSucc := by
      rw [h1]
      exact fun h => hij (Fin.castSucc_injective m h)
    rw [if_neg h2]
    ring
  · rw [if_neg h1]
    ring

theorem congruenceIdeal_le_ker : congruenceIdeal a m ≤ RingHom.ker (congruenceEval a m) := by
  rw [congruenceIdeal, Ideal.span_le]
  rintro f (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · rw [SetLike.mem_coe, RingHom.mem_ker]
    show congruenceEval a m (X i ^ 2 - C a * X i) = 0
    rw [map_sub, map_pow, map_mul, congruenceEval, aeval_X, aeval_C, pow_two,
      congruenceGen_mul_self, Algebra.smul_def]
    simp
  · rw [SetLike.mem_coe, RingHom.mem_ker]
    show congruenceEval a m (X i * X j) = 0
    rw [map_mul, congruenceEval, aeval_X, aeval_X, congruenceGen_mul_of_ne hij]

/-- The linear normal form `c₀ + ∑ cᵢ Xᵢ`. -/
noncomputable def linForm (c₀ : R) (c : Fin m → R) : MvPolynomial (Fin m) R :=
  C c₀ + ∑ i, C (c i) * X i

theorem linForm_add (c₀ d₀ : R) (c d : Fin m → R) :
    linForm (c₀ + d₀) (c + d) = linForm c₀ c + linForm d₀ d := by
  simp only [linForm, map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- **Card `(15)`, reduction step.**  Every polynomial is congruent modulo the relations to a
linear normal form: monomials of degree at least two all reduce. -/
theorem exists_linForm (f : MvPolynomial (Fin m) R) :
    ∃ (c₀ : R) (c : Fin m → R), f - linForm c₀ c ∈ congruenceIdeal a m := by
  classical
  induction f using MvPolynomial.induction_on with
  | C r => exact ⟨r, 0, by simp [linForm]⟩
  | add p q hp hq =>
    obtain ⟨c₀, c, hc⟩ := hp
    obtain ⟨d₀, d, hd⟩ := hq
    refine ⟨c₀ + d₀, c + d, ?_⟩
    rw [linForm_add]
    have hsplit : p + q - (linForm c₀ c + linForm d₀ d)
        = (p - linForm c₀ c) + (q - linForm d₀ d) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ hc hd
  | mul_X p i hp =>
    obtain ⟨c₀, c, hc⟩ := hp
    refine ⟨0, Pi.single i (c₀ + a * c i), ?_⟩
    have hterm : ∀ j : Fin m,
        C (c j) * X j * X i - (if j = i then C (c i) * (C a * X i) else 0)
          ∈ congruenceIdeal a m := by
      intro j
      by_cases hji : j = i
      · subst hji
        have hrel : (X j ^ 2 - C a * X j) ∈ congruenceIdeal a m :=
          Ideal.subset_span (Or.inl ⟨j, rfl⟩)
        have heq : C (c j) * X j * X j - (if j = j then C (c j) * (C a * X j) else 0)
            = C (c j) * (X j ^ 2 - C a * X j) := by
          rw [if_pos rfl]; ring
        rw [heq]
        exact Ideal.mul_mem_left _ _ hrel
      · have hrel : (X j * X i) ∈ congruenceIdeal a m :=
          Ideal.subset_span (Or.inr ⟨j, i, hji, rfl⟩)
        have heq : C (c j) * X j * X i - (if j = i then C (c i) * (C a * X i) else 0)
            = C (c j) * (X j * X i) := by
          rw [if_neg hji]; ring
        rw [heq]
        exact Ideal.mul_mem_left _ _ hrel
    have hsum : (∑ j, C (c j) * X j) * X i - C (c i) * (C a * X i) ∈ congruenceIdeal a m := by
      have hs := Ideal.sum_mem (congruenceIdeal a m) (fun j (_ : j ∈ Finset.univ) => hterm j)
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i
        (fun _ => C (c i) * (C a * X i)), if_pos (Finset.mem_univ i)] at hs
      rw [Finset.sum_mul]
      exact hs
    have hnf : linForm 0 (Pi.single i (c₀ + a * c i)) = C c₀ * X i + C (c i) * (C a * X i) := by
      simp only [linForm, map_zero, zero_add]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun h => absurd (Finset.mem_univ i) h)]
      simp only [Pi.single_eq_same, map_add, map_mul]
      ring
    rw [hnf]
    have hsplit : p * X i - (C c₀ * X i + C (c i) * (C a * X i))
        = (p - linForm c₀ c) * X i
          + ((∑ j, C (c j) * X j) * X i - C (c i) * (C a * X i)) := by
      simp only [linForm]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc) hsum

theorem congruenceEval_linForm_apply (c₀ : R) (c : Fin m → R) (l : Fin (m + 1)) :
    congruenceEval a m (linForm c₀ c) l
      = c₀ + ∑ j, (if l = j.castSucc then a * c j else 0) := by
  classical
  simp [linForm, congruenceEval, congruenceGen, Pi.single_apply]

theorem congruenceEval_linForm_castSucc (c₀ : R) (c : Fin m → R) (i : Fin m) :
    congruenceEval a m (linForm c₀ c) i.castSucc = c₀ + a * c i := by
  classical
  rw [congruenceEval_linForm_apply, Finset.sum_eq_single i
    (fun j _ hj => by rw [if_neg (fun h => hj (Fin.castSucc_injective m h.symm))])
    (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]

theorem congruenceEval_linForm_last (c₀ : R) (c : Fin m → R) :
    congruenceEval a m (linForm c₀ c) (Fin.last m) = c₀ := by
  classical
  rw [congruenceEval_linForm_apply, Finset.sum_congr rfl
    (fun j _ => by rw [if_neg (fun h => absurd h.symm (Fin.castSucc_lt_last j).ne)])]
  simp

theorem congruenceGen_mem (i : Fin m) : congruenceGen a m i ∈ congruenceOrder a (m + 1) := by
  intro l l'
  simp only [congruenceGen, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  exact ⟨(if l = i.castSucc then 1 else 0) - (if l' = i.castSucc then 1 else 0), by ring⟩

theorem range_congruenceEval :
    (congruenceEval a m).range = congruenceOrder a (m + 1) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [congruenceEval, ← Algebra.adjoin_range_eq_range_aeval]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    exact congruenceGen_mem i
  · rintro v hv
    choose c hc using fun i : Fin m => hv i.castSucc (Fin.last m)
    refine ⟨linForm (v (Fin.last m)) c, ?_⟩
    show congruenceEval a m (linForm (v (Fin.last m)) c) = v
    funext l
    induction l using Fin.lastCases with
    | last => rw [congruenceEval_linForm_last]
    | cast i =>
      rw [congruenceEval_linForm_castSucc, ← hc i]
      ring

variable [IsDomain R]

theorem ker_congruenceEval (ha : a ≠ 0) :
    RingHom.ker (congruenceEval a m) = congruenceIdeal a m := by
  refine le_antisymm ?_ congruenceIdeal_le_ker
  intro f hf
  obtain ⟨c₀, c, hc⟩ := exists_linForm (a := a) f
  have hg : congruenceEval a m (linForm c₀ c) = 0 := by
    have h1 : congruenceEval a m (f - linForm c₀ c) = 0 :=
      RingHom.mem_ker.1 (congruenceIdeal_le_ker hc)
    rw [map_sub, RingHom.mem_ker.1 hf, zero_sub, neg_eq_zero] at h1
    exact h1
  have h0 : c₀ = 0 := by
    have := congrFun hg (Fin.last m)
    rwa [congruenceEval_linForm_last] at this
  have hci : ∀ i, c i = 0 := by
    intro i
    have h := congrFun hg i.castSucc
    rw [congruenceEval_linForm_castSucc, h0, zero_add] at h
    exact (mul_eq_zero.1 h).resolve_left ha
  have : linForm c₀ c = 0 := by
    simp only [linForm, h0, map_zero, zero_add]
    exact Finset.sum_eq_zero fun i _ => by rw [hci i, map_zero, zero_mul]
  rwa [this, sub_zero] at hc

/-- Corestriction of the evaluation map to the congruence order. -/
noncomputable def congruenceEvalRestrict :
    MvPolynomial (Fin m) R →ₐ[R] congruenceOrder a (m + 1) :=
  (congruenceEval a m).codRestrict _ fun x =>
    range_congruenceEval (a := a) (m := m) ▸ (AlgHom.mem_range _).2 ⟨x, rfl⟩

omit [IsDomain R] in
theorem congruenceEvalRestrict_surjective :
    Function.Surjective (congruenceEvalRestrict (a := a) (m := m)) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).1 ((range_congruenceEval (a := a) (m := m)).ge hy)
  exact ⟨x, Subtype.ext hx⟩

omit [IsDomain R] in
theorem ker_congruenceEvalRestrict :
    RingHom.ker (congruenceEvalRestrict (a := a) (m := m))
      = RingHom.ker (congruenceEval a m) :=
  SetLike.ext fun x => by
    simp [RingHom.mem_ker, congruenceEvalRestrict, AlgHom.codRestrict, Subtype.ext_iff]

/-- **Card `(15)`.**  The diagonal congruence order is presented by `m` generators, each
idempotent up to `a`, annihilating one another. -/
noncomputable def congruencePresentation (ha : a ≠ 0) :
    (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ≃ₐ[R] congruenceOrder a (m + 1) :=
  (Ideal.quotientEquivAlgOfEq R
      ((ker_congruenceEvalRestrict.trans (ker_congruenceEval ha)).symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective congruenceEvalRestrict_surjective)

end Presentation

/-! ## The cotangent module of the congruence order -/

section Kaehler

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

/-- The class of the `i`-th generator in the presented congruence order. -/
noncomputable def congruenceX (a : R) (m : ℕ) (i : Fin m) :
    MvPolynomial (Fin m) R ⧸ congruenceIdeal a m :=
  Ideal.Quotient.mk _ (X i)

theorem algebraMap_congruenceQuotient (r : R) :
    algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r
      = Ideal.Quotient.mk _ (C r) := rfl

theorem congruenceX_sq (i : Fin m) :
    congruenceX a m i * congruenceX a m i
      = algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a * congruenceX a m i := by
  have hrel : (X i ^ 2 - C a * X i : MvPolynomial (Fin m) R) ∈ congruenceIdeal a m :=
    Ideal.subset_span (Or.inl ⟨i, rfl⟩)
  have := Ideal.Quotient.eq_zero_iff_mem.2 hrel
  rw [map_sub, sub_eq_zero, map_pow, map_mul] at this
  simpa [congruenceX, pow_two, algebraMap_congruenceQuotient] using this

theorem congruenceX_mul_of_ne {i j : Fin m} (hij : i ≠ j) :
    congruenceX a m i * congruenceX a m j = 0 := by
  have hrel : (X i * X j : MvPolynomial (Fin m) R) ∈ congruenceIdeal a m :=
    Ideal.subset_span (Or.inr ⟨i, j, hij, rfl⟩)
  have := Ideal.Quotient.eq_zero_iff_mem.2 hrel
  rwa [map_mul] at this

/-- The relation vectors of the cotangent presentation: the differentiated defining relations. -/
noncomputable def kaehlerRelationSet (a : R) (m : ℕ) :
    Set (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :=
  {v | (∃ i, v = Pi.single i (congruenceX a m i + congruenceX a m i -
          algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a)) ∨
    ∃ i j, i ≠ j ∧ v = Pi.single i (congruenceX a m j) + Pi.single j (congruenceX a m i)}

/-- The relation submodule of the cotangent presentation. -/
noncomputable def kaehlerRelations (a : R) (m : ℕ) :
    Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :=
  Submodule.span _ (kaehlerRelationSet a m)

/-- Evaluation of a coefficient vector against the differentials of the generators. -/
noncomputable def kaehlerEval :
    (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m]
      Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] :=
  ∑ i : Fin m, (LinearMap.proj i).smulRight
    (KaehlerDifferential.D R _ (congruenceX a m i))

theorem kaehlerEval_single (i : Fin m)
    (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :
    kaehlerEval (a := a) (m := m) (Pi.single i c)
      = c • KaehlerDifferential.D R _ (congruenceX a m i) := by
  classical
  simp only [kaehlerEval, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Pi.single_apply, ite_smul]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hj
    rw [if_neg hj]
    exact zero_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      (KaehlerDifferential.D R _ (congruenceX a m j))
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem kaehlerRelations_le_ker :
    kaehlerRelations a m ≤ LinearMap.ker (kaehlerEval (a := a) (m := m)) := by
  rw [kaehlerRelations, Submodule.span_le]
  rintro v (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · rw [SetLike.mem_coe, LinearMap.mem_ker, kaehlerEval_single]
    have hsq := congrArg (KaehlerDifferential.D R
      (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) (congruenceX_sq (a := a) i)
    rw [Derivation.leibniz, Derivation.leibniz, Derivation.map_algebraMap, smul_zero,
      add_zero] at hsq
    rw [sub_smul, add_smul]
    exact sub_eq_zero.2 hsq
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_add, kaehlerEval_single, kaehlerEval_single]
    have hz := congrArg (KaehlerDifferential.D R
      (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) (congruenceX_mul_of_ne (a := a) hij)
    rw [Derivation.leibniz, map_zero] at hz
    rw [add_comm]
    exact hz

/-- The comparison map from the cotangent model to the Kähler module. -/
noncomputable def modelToKaehler :
    ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m]
      Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] :=
  Submodule.liftQ _ kaehlerEval kaehlerRelations_le_ker

/-- The tautological derivation of the polynomial ring into the cotangent model. -/
noncomputable def modelDerivation :
    Derivation R (MvPolynomial (Fin m) R)
      ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :=
  MvPolynomial.mkDerivation R fun i =>
    Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i 1)

theorem modelDerivation_X (i : Fin m) :
    modelDerivation (a := a) (m := m) (X i)
      = Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i 1) :=
  MvPolynomial.mkDerivation_X _ _ _

theorem congruenceIdeal_smul_eq_zero {x : MvPolynomial (Fin m) R}
    (hx : x ∈ congruenceIdeal a m)
    (w : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :
    x • w = 0 := by
  rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) x w,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  exact zero_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) w

theorem model_single (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (i : Fin m) :
    Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i c)
      = c • Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i 1) := by
  classical
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem model_smul_gen (q : MvPolynomial (Fin m) R) (i : Fin m) :
    q • Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i 1)
      = Ideal.Quotient.mk (congruenceIdeal a m) q
          • Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i 1) := by
  rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) q,
    Ideal.Quotient.algebraMap_eq]

theorem modelDerivation_eq_zero_of_mem {f : MvPolynomial (Fin m) R}
    (hf : f ∈ congruenceIdeal a m) : modelDerivation (a := a) (m := m) f = 0 := by
  rw [congruenceIdeal] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
    · rw [map_sub, pow_two, Derivation.leibniz, Derivation.leibniz, modelDerivation_X,
        show (C a : MvPolynomial (Fin m) R) = algebraMap R _ a from rfl,
        Derivation.map_algebraMap, smul_zero, add_zero, model_smul_gen, model_smul_gen]
      have hcx : Ideal.Quotient.mk (congruenceIdeal a m) (X i) = congruenceX a m i := rfl
      have hca : Ideal.Quotient.mk (congruenceIdeal a m)
          (algebraMap R (MvPolynomial (Fin m) R) a)
            = algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a := rfl
      rw [hcx, hca]
      have hz := (Submodule.Quotient.mk_eq_zero (kaehlerRelations a m)).2
        (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
      rw [model_single, sub_smul, add_smul] at hz
      exact hz
    · rw [Derivation.leibniz, modelDerivation_X, modelDerivation_X, model_smul_gen,
        model_smul_gen]
      have hcx : ∀ l : Fin m,
          Ideal.Quotient.mk (congruenceIdeal a m) (X l) = congruenceX a m l := fun _ => rfl
      rw [hcx, hcx, ← model_single, ← model_single, ← Submodule.Quotient.mk_add]
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.subset_span (Or.inr ⟨j, i, hij.symm, by rw [add_comm]⟩))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x hx hr =>
    rw [smul_eq_mul, Derivation.leibniz, hr, smul_zero, zero_add,
      congruenceIdeal_smul_eq_zero hx (modelDerivation r)]

/-- The induced derivation of the presented order into the cotangent model. -/
noncomputable def quotDerivation :
    Derivation R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :=
  Derivation.mk'
    (Submodule.liftQ ((congruenceIdeal a m).restrictScalars R)
      (modelDerivation (a := a) (m := m)).toLinearMap
      (fun _ hx => modelDerivation_eq_zero_of_mem hx))
    (by
      intro u v
      induction u using Quotient.inductionOn' with
      | h f =>
        induction v using Quotient.inductionOn' with
        | h g =>
          show modelDerivation (f * g) = _
          rw [Derivation.leibniz]
          rw [← IsScalarTower.algebraMap_smul
              (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) f (modelDerivation g),
            ← IsScalarTower.algebraMap_smul
              (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) g (modelDerivation f)]
          rfl)

theorem quotDerivation_mk (f : MvPolynomial (Fin m) R) :
    quotDerivation (a := a) (m := m) (Ideal.Quotient.mk _ f) = modelDerivation f := rfl

theorem quotDerivation_congruenceX (i : Fin m) :
    quotDerivation (a := a) (m := m) (congruenceX a m i)
      = Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i 1) :=
  modelDerivation_X i

/-- The comparison map from the Kähler module to the cotangent model. -/
noncomputable def kaehlerToModel :
    Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m]
      ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :=
  (quotDerivation (a := a) (m := m)).liftKaehlerDifferential

theorem kaehlerToModel_D (i : Fin m) :
    kaehlerToModel (KaehlerDifferential.D R _ (congruenceX a m i))
      = Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i 1) := by
  rw [kaehlerToModel, Derivation.liftKaehlerDifferential_comp_D, quotDerivation_congruenceX]

theorem modelToKaehler_mk (v : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :
    modelToKaehler (Submodule.Quotient.mk (p := kaehlerRelations a m) v) = kaehlerEval v := rfl

theorem adjoin_congruenceX_eq_top :
    Algebra.adjoin R (Set.range (congruenceX a m)) = ⊤ := by
  have himg : Set.range (congruenceX a m)
      = (Ideal.Quotient.mkₐ R (congruenceIdeal a m)) ''
        (Set.range (X : Fin m → MvPolynomial (Fin m) R)) := by
    rw [← Set.range_comp]
    rfl
  rw [himg, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top,
    (AlgHom.range_eq_top _).2 Ideal.Quotient.mk_surjective]

/-- **Card `(16)`.**  The Kähler module of the congruence order is exactly the cotangent model:
the differentiated relations generate all relations between the `dxᵢ`. -/
noncomputable def kaehlerModelEquiv :
    Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      ≃ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m]
      ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) := by
  classical
  refine LinearEquiv.ofLinear kaehlerToModel modelToKaehler ?_ ?_
  · refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (kaehlerRelations a m) x
    have hmk : Submodule.Quotient.mk (p := kaehlerRelations a m) v
        = ∑ i, Submodule.Quotient.mk (p := kaehlerRelations a m) (Pi.single i (v i)) := by
      simp only [← Submodule.mkQ_apply, ← map_sum]
      exact congrArg _ (Finset.univ_sum_single v).symm
    rw [LinearMap.comp_apply, LinearMap.id_apply, hmk, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [modelToKaehler_mk, kaehlerEval_single, map_smul, kaehlerToModel_D, ← model_single]
  · have hder : (modelToKaehler.compDer (quotDerivation (a := a) (m := m)))
        = KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) := by
      refine Derivation.ext_of_adjoin_eq_top _ adjoin_congruenceX_eq_top ?_
      rintro _ ⟨i, rfl⟩
      show modelToKaehler (quotDerivation (congruenceX a m i)) = _
      rw [quotDerivation_congruenceX, modelToKaehler_mk, kaehlerEval_single, one_smul]
    refine LinearMap.ext fun x => ?_
    have hspan := KaehlerDifferential.span_range_derivation (R := R)
      (S := MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
    have hx : x ∈ Submodule.span (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        (Set.range (KaehlerDifferential.D R _)) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, rfl⟩ := hy
      show modelToKaehler (kaehlerToModel _) = _
      rw [kaehlerToModel, Derivation.liftKaehlerDifferential_comp_D]
      exact Derivation.congr_fun hder u
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | smul c y _ hy => simp only [map_smul, hy]

/-! ### The free `R`-basis of the order -/

theorem linForm_smul (r c₀ : R) (c : Fin m → R) :
    linForm (r * c₀) (r • c) = C r * linForm c₀ c := by
  simp only [linForm, mul_add, Finset.mul_sum, map_mul, Pi.smul_apply, smul_eq_mul]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- The normal form as a linear map into the polynomial ring. -/
noncomputable def linFormMap : (R × (Fin m → R)) →ₗ[R] MvPolynomial (Fin m) R :=
  LinearMap.coprod (LinearMap.toSpanSingleton R _ 1)
    (Fintype.linearCombination R (X : Fin m → MvPolynomial (Fin m) R))

theorem linFormMap_apply (p : R × (Fin m → R)) : linFormMap p = linForm p.1 p.2 := by
  simp only [linFormMap, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
    Fintype.linearCombination_apply, linForm, smul_eq_C_mul, mul_one]

/-- The normal-form coordinates as a linear map into the order. -/
noncomputable def linFormLinear :
    (R × (Fin m → R)) →ₗ[R] MvPolynomial (Fin m) R ⧸ congruenceIdeal a m :=
  (Ideal.Quotient.mkₐ R (congruenceIdeal a m)).toLinearMap ∘ₗ linFormMap

theorem linFormLinear_apply (p : R × (Fin m → R)) :
    linFormLinear (a := a) p = Ideal.Quotient.mk _ (linForm p.1 p.2) := by
  show Ideal.Quotient.mk _ (linFormMap p) = _
  rw [linFormMap_apply]

variable [IsDomain R]

/-- **Card `(15)`, freeness.**  The order is `R`-free with basis `1, x₁, …, x_m`. -/
noncomputable def congruenceCoordEquiv (ha : a ≠ 0) :
    (R × (Fin m → R)) ≃ₗ[R] MvPolynomial (Fin m) R ⧸ congruenceIdeal a m :=
  LinearEquiv.ofBijective linFormLinear
    ⟨by
      intro p q hpq
      have hmem : linForm p.1 p.2 - linForm q.1 q.2 ∈ congruenceIdeal a m := by
        rw [← Ideal.Quotient.eq]
        rw [linFormLinear_apply, linFormLinear_apply] at hpq
        exact hpq
      rw [← ker_congruenceEval ha, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
      have h0 := congrFun hmem (Fin.last m)
      rw [congruenceEval_linForm_last, congruenceEval_linForm_last] at h0
      refine Prod.ext h0 (funext fun i => ?_)
      have hi := congrFun hmem i.castSucc
      rw [congruenceEval_linForm_castSucc, congruenceEval_linForm_castSucc, h0,
        add_right_inj] at hi
      exact (mul_right_cancel₀ ha (by rw [mul_comm, hi, mul_comm]) : p.2 i = q.2 i),
     by
      intro y
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨c₀, c, hc⟩ := exists_linForm (a := a) f
      exact ⟨(c₀, c), by rw [linFormLinear_apply]; exact (Ideal.Quotient.eq.2 hc).symm⟩⟩

end Kaehler

/-! ## The diagonal and antisymmetric cotangent sectors

The cotangent model splits into a diagonal sector `(R/a²)^m`, carrying the classes of the
differentials `dxᵢ`, and an antisymmetric sector `(R/a)^{binom m 2}`, carrying the classes
`xⱼ dxᵢ = −xᵢ dxⱼ` for `i < j`.
-/

section Splitting

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

/-- Index set of the antisymmetric cotangent sector: strictly ordered pairs of sheets. -/
abbrev pairIndex (m : ℕ) : Type := {p : Fin m × Fin m // p.1 < p.2}

/-- The diagonal-plus-antisymmetric model of the cotangent module. -/
abbrev cotangentModel (a : R) (m : ℕ) : Type _ :=
  (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) × (pairIndex m → R ⧸ Ideal.span ({a} : Set R))

/-- The diagonal coordinate `cᵢ + (a/2)·dᵢᵢ` of a coordinate vector. -/
noncomputable def coordDiag [Invertible (2 : R)] (a : R) (i : Fin m) :
    (Fin m → R × (Fin m → R)) →ₗ[R] R :=
  (LinearMap.fst R R (Fin m → R)).comp (LinearMap.proj i) +
    (⅟(2 : R) * a) •
      ((LinearMap.proj i).comp
        ((LinearMap.snd R R (Fin m → R)).comp (LinearMap.proj i)))

theorem coordDiag_apply [Invertible (2 : R)] (i : Fin m) (w : Fin m → R × (Fin m → R)) :
    coordDiag a i w = (w i).1 + ⅟(2 : R) * a * (w i).2 i := rfl

/-- The antisymmetric coordinate `d_{ij} − d_{ji}` of a coordinate vector. -/
noncomputable def coordPair (p : pairIndex m) :
    (Fin m → R × (Fin m → R)) →ₗ[R] R :=
  (LinearMap.proj p.1.2).comp
      ((LinearMap.snd R R (Fin m → R)).comp (LinearMap.proj p.1.1)) -
    (LinearMap.proj p.1.1).comp
      ((LinearMap.snd R R (Fin m → R)).comp (LinearMap.proj p.1.2))

theorem coordPair_apply (p : pairIndex m) (w : Fin m → R × (Fin m → R)) :
    coordPair p w = (w p.1.1).2 p.1.2 - (w p.1.2).2 p.1.1 := rfl

/-- The splitting of coordinate vectors into the diagonal and antisymmetric sectors. -/
noncomputable def coordSplit [Invertible (2 : R)] (a : R) (m : ℕ) :
    (Fin m → R × (Fin m → R)) →ₗ[R] cotangentModel a m :=
  (LinearMap.pi fun i => (Ideal.span ({a ^ 2} : Set R)).mkQ.comp (coordDiag a i)).prod
    (LinearMap.pi fun p : pairIndex m => (Ideal.span ({a} : Set R)).mkQ.comp (coordPair p))

theorem coordSplit_fst [Invertible (2 : R)] (w : Fin m → R × (Fin m → R)) (i : Fin m) :
    (coordSplit a m w).1 i = Submodule.Quotient.mk ((w i).1 + ⅟(2 : R) * a * (w i).2 i) := rfl

theorem coordSplit_snd [Invertible (2 : R)] (w : Fin m → R × (Fin m → R)) (p : pairIndex m) :
    (coordSplit a m w).2 p
      = Submodule.Quotient.mk ((w p.1.1).2 p.1.2 - (w p.1.2).2 p.1.1) := rfl

variable [IsDomain R]

theorem congruenceCoordEquiv_apply (ha : a ≠ 0) (p : R × (Fin m → R)) :
    congruenceCoordEquiv (a := a) (m := m) ha p = Ideal.Quotient.mk _ (linForm p.1 p.2) :=
  linFormLinear_apply p

theorem congruenceCoordEquiv_one (ha : a ≠ 0) :
    congruenceCoordEquiv (a := a) (m := m) ha (1, 0) = 1 := by
  rw [congruenceCoordEquiv_apply]
  have h : linForm (1 : R) (0 : Fin m → R) = 1 := by simp [linForm]
  rw [h, map_one]

theorem congruenceCoordEquiv_gen (ha : a ≠ 0) (k : Fin m) :
    congruenceCoordEquiv (a := a) (m := m) ha (0, Pi.single k 1) = congruenceX a m k := by
  classical
  rw [congruenceCoordEquiv_apply]
  have h : linForm (0 : R) (Pi.single k (1 : R)) = X k := by
    simp only [linForm, map_zero, zero_add]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp
  rw [h]
  rfl

theorem congruenceCoordEquiv_symm_one (ha : a ≠ 0) :
    (congruenceCoordEquiv (a := a) (m := m) ha).symm 1 = (1, 0) := by
  rw [LinearEquiv.symm_apply_eq]
  exact (congruenceCoordEquiv_one ha).symm

theorem congruenceCoordEquiv_symm_gen (ha : a ≠ 0) (k : Fin m) :
    (congruenceCoordEquiv (a := a) (m := m) ha).symm (congruenceX a m k) = (0, Pi.single k 1) := by
  rw [LinearEquiv.symm_apply_eq]
  exact (congruenceCoordEquiv_gen ha k).symm

/-- The coordinate isomorphism `Aᵐ ≃ (R × Rᵐ)ᵐ` induced by the `R`-basis `1, x₁, …, x_m`. -/
noncomputable def congruenceCoordPi (ha : a ≠ 0) :
    (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ≃ₗ[R] (Fin m → R × (Fin m → R)) :=
  LinearEquiv.piCongrRight fun _ => (congruenceCoordEquiv (a := a) (m := m) ha).symm

theorem congruenceCoordPi_apply (ha : a ≠ 0)
    (v : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (i : Fin m) :
    congruenceCoordPi ha v i = (congruenceCoordEquiv (a := a) (m := m) ha).symm (v i) := rfl

/-- The splitting map on the free module `Aᵐ` of cotangent coefficient vectors. -/
noncomputable def kaehlerSplitRaw [Invertible (2 : R)] (ha : a ≠ 0) :
    (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) →ₗ[R] cotangentModel a m :=
  (coordSplit a m).comp (congruenceCoordPi ha).toLinearMap

theorem kaehlerSplitRaw_fst [Invertible (2 : R)] (ha : a ≠ 0)
    (v : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (i : Fin m) :
    (kaehlerSplitRaw ha v).1 i
      = Submodule.Quotient.mk
          (((congruenceCoordEquiv (a := a) (m := m) ha).symm (v i)).1
            + ⅟(2 : R) * a * ((congruenceCoordEquiv (a := a) (m := m) ha).symm (v i)).2 i) := rfl

theorem kaehlerSplitRaw_snd [Invertible (2 : R)] (ha : a ≠ 0)
    (v : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (p : pairIndex m) :
    (kaehlerSplitRaw ha v).2 p
      = Submodule.Quotient.mk
          (((congruenceCoordEquiv (a := a) (m := m) ha).symm (v p.1.1)).2 p.1.2
            - ((congruenceCoordEquiv (a := a) (m := m) ha).symm (v p.1.2)).2 p.1.1) := rfl

theorem congruenceCoordPi_single (ha : a ≠ 0) (i : Fin m)
    (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (j : Fin m) :
    (congruenceCoordEquiv (a := a) (m := m) ha).symm
        ((Pi.single i c : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) j)
      = if j = i then (congruenceCoordEquiv (a := a) (m := m) ha).symm c else 0 := by
  classical
  by_cases h : j = i
  · subst h; rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne h, map_zero, if_neg h]

theorem kaehlerSplitRaw_single_fst [Invertible (2 : R)] (ha : a ≠ 0) (i : Fin m)
    (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (j : Fin m) :
    (kaehlerSplitRaw ha (Pi.single i c)).1 j
      = if j = i then
          Submodule.Quotient.mk
            (((congruenceCoordEquiv (a := a) (m := m) ha).symm c).1
              + ⅟(2 : R) * a * ((congruenceCoordEquiv (a := a) (m := m) ha).symm c).2 j)
        else 0 := by
  classical
  rw [kaehlerSplitRaw_fst, congruenceCoordPi_single]
  by_cases h : j = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    show Submodule.Quotient.mk ((0 : R) + ⅟(2 : R) * a * (0 : R)) = 0
    simp

theorem kaehlerSplitRaw_single_snd [Invertible (2 : R)] (ha : a ≠ 0) (i : Fin m)
    (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (p : pairIndex m) :
    (kaehlerSplitRaw ha (Pi.single i c)).2 p
      = Submodule.Quotient.mk
          ((if p.1.1 = i then ((congruenceCoordEquiv (a := a) (m := m) ha).symm c).2 p.1.2
              else 0)
            - (if p.1.2 = i then ((congruenceCoordEquiv (a := a) (m := m) ha).symm c).2 p.1.1
              else 0)) := by
  classical
  rw [kaehlerSplitRaw_snd, congruenceCoordPi_single, congruenceCoordPi_single]
  congr 1
  by_cases h1 : p.1.1 = i <;> by_cases h2 : p.1.2 = i <;> simp [h1, h2]

theorem kaehlerSplitRaw_single_one [Invertible (2 : R)] (ha : a ≠ 0) (i : Fin m) :
    kaehlerSplitRaw ha (Pi.single i (1 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m))
      = (Pi.single i (Submodule.Quotient.mk 1), 0) := by
  classical
  refine Prod.ext (funext fun j => ?_) (funext fun p => ?_)
  · rw [kaehlerSplitRaw_single_fst, congruenceCoordEquiv_symm_one]
    by_cases h : j = i <;> simp [h]
  · rw [kaehlerSplitRaw_single_snd, congruenceCoordEquiv_symm_one]
    simp

/-- The image of the generator `xₖ eᵢ` in the diagonal sector. -/
theorem kaehlerSplitRaw_singleGen_fst [Invertible (2 : R)] (ha : a ≠ 0) (i k j : Fin m) :
    (kaehlerSplitRaw ha (Pi.single i (congruenceX a m k))).1 j
      = if j = i then
          Submodule.Quotient.mk (⅟(2 : R) * a * (if j = k then (1 : R) else 0)) else 0 := by
  classical
  rw [kaehlerSplitRaw_single_fst, congruenceCoordEquiv_symm_gen]
  by_cases h : j = i <;> simp [h, Pi.single_apply]

/-- The image of the generator `xₖ eᵢ` in the antisymmetric sector. -/
theorem kaehlerSplitRaw_singleGen_snd [Invertible (2 : R)] (ha : a ≠ 0) (i k : Fin m)
    (p : pairIndex m) :
    (kaehlerSplitRaw ha (Pi.single i (congruenceX a m k))).2 p
      = Submodule.Quotient.mk
          ((if p.1.1 = i ∧ p.1.2 = k then (1 : R) else 0)
            - (if p.1.2 = i ∧ p.1.1 = k then (1 : R) else 0)) := by
  classical
  rw [kaehlerSplitRaw_single_snd, congruenceCoordEquiv_symm_gen]
  congr 1
  show (if p.1.1 = i then (Pi.single k (1 : R) : Fin m → R) p.1.2 else 0)
      - (if p.1.2 = i then (Pi.single k (1 : R) : Fin m → R) p.1.1 else 0)
      = (if p.1.1 = i ∧ p.1.2 = k then (1 : R) else 0)
        - (if p.1.2 = i ∧ p.1.1 = k then (1 : R) else 0)
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

theorem kaehlerSplitRaw_single_self [Invertible (2 : R)] (ha : a ≠ 0) (i : Fin m) :
    kaehlerSplitRaw ha (Pi.single i (congruenceX a m i))
      = (Pi.single i (Submodule.Quotient.mk (⅟(2 : R) * a)), 0) := by
  classical
  refine Prod.ext (funext fun j => ?_) (funext fun p => ?_)
  · rw [kaehlerSplitRaw_singleGen_fst]
    by_cases h : j = i <;> simp [h]
  · rw [kaehlerSplitRaw_singleGen_snd]
    have hlt : p.1.1 < p.1.2 := p.2
    have h1 : ¬ (p.1.1 = i ∧ p.1.2 = i) := by
      rintro ⟨e1, e2⟩
      rw [e1, e2] at hlt
      exact lt_irrefl _ hlt
    have h2 : ¬ (p.1.2 = i ∧ p.1.1 = i) := by
      rintro ⟨e1, e2⟩
      rw [e1, e2] at hlt
      exact lt_irrefl _ hlt
    rw [if_neg h1, if_neg h2]
    simp

theorem kaehlerSplitRaw_single_lt [Invertible (2 : R)] (ha : a ≠ 0) {i k : Fin m} (hik : i < k) :
    kaehlerSplitRaw ha (Pi.single i (congruenceX a m k))
      = (0, Pi.single (⟨(i, k), hik⟩ : pairIndex m) (Submodule.Quotient.mk 1)) := by
  classical
  refine Prod.ext (funext fun j => ?_) (funext fun p => ?_)
  · rw [kaehlerSplitRaw_singleGen_fst]
    by_cases h : j = i
    · rw [if_pos h, if_neg (by rw [h]; exact hik.ne)]
      simp
    · rw [if_neg h]
      simp
  · rw [kaehlerSplitRaw_singleGen_snd]
    show _ = (Pi.single (ι := pairIndex m) (M := fun _ => R ⧸ Ideal.span ({a} : Set R))
      ⟨(i, k), hik⟩ (Submodule.Quotient.mk (1 : R))) p
    rw [Pi.single_apply]
    have hlt : p.1.1 < p.1.2 := p.2
    have hp : (p = (⟨(i, k), hik⟩ : pairIndex m)) ↔ (p.1.1 = i ∧ p.1.2 = k) := by
      rw [Subtype.ext_iff, Prod.ext_iff]
    have hfalse : ¬ (p.1.2 = i ∧ p.1.1 = k) := by
      rintro ⟨e1, e2⟩
      rw [e1, e2] at hlt
      exact absurd hlt (lt_asymm hik)
    rw [if_neg hfalse, sub_zero]
    by_cases h1 : p.1.1 = i ∧ p.1.2 = k
    · rw [if_pos h1, if_pos (hp.2 h1)]
    · rw [if_neg h1, if_neg (fun hc => h1 (hp.1 hc))]
      simp

theorem kaehlerSplitRaw_single_gt [Invertible (2 : R)] (ha : a ≠ 0) {i k : Fin m} (hik : k < i) :
    kaehlerSplitRaw ha (Pi.single i (congruenceX a m k))
      = (0, -Pi.single (⟨(k, i), hik⟩ : pairIndex m) (Submodule.Quotient.mk 1)) := by
  classical
  refine Prod.ext (funext fun j => ?_) (funext fun p => ?_)
  · rw [kaehlerSplitRaw_singleGen_fst]
    by_cases h : j = i
    · rw [if_pos h, if_neg (by rw [h]; exact hik.ne')]
      simp
    · rw [if_neg h]
      simp
  · rw [kaehlerSplitRaw_singleGen_snd]
    show _ = -((Pi.single (ι := pairIndex m) (M := fun _ => R ⧸ Ideal.span ({a} : Set R))
      ⟨(k, i), hik⟩ (Submodule.Quotient.mk (1 : R))) p)
    rw [Pi.single_apply]
    have hlt : p.1.1 < p.1.2 := p.2
    have hp : (p = (⟨(k, i), hik⟩ : pairIndex m)) ↔ (p.1.1 = k ∧ p.1.2 = i) := by
      rw [Subtype.ext_iff, Prod.ext_iff]
    have hfalse : ¬ (p.1.1 = i ∧ p.1.2 = k) := by
      rintro ⟨e1, e2⟩
      rw [e1, e2] at hlt
      exact absurd hlt (lt_asymm hik)
    rw [if_neg hfalse]
    by_cases h1 : p.1.2 = i ∧ p.1.1 = k
    · rw [if_pos h1, if_pos (hp.2 ⟨h1.2, h1.1⟩)]
      simp
    · rw [if_neg h1, if_neg (fun hc => h1 ⟨(hp.1 hc).2, (hp.1 hc).1⟩)]
      simp

end Splitting

/-! ## The relation submodule in `R`-generators -/

section Relations

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

private theorem smul_single (c x : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (i : Fin m) :
    c • (Pi.single i x : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      = Pi.single i (c * x) := by
  classical
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem aSmul_single (i k : Fin m) :
    a • (Pi.single i (congruenceX a m k)
        : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      = Pi.single i (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a
          * congruenceX a m k) := by
  rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a,
    smul_single]

/-- The differentiated square relation `(2xᵢ − a)·eᵢ`. -/
noncomputable def sqRelation (a : R) (m : ℕ) (i : Fin m) :
    Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m :=
  Pi.single i (congruenceX a m i + congruenceX a m i
    - algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a)

/-- The differentiated cross relation `xⱼ·eᵢ + xᵢ·eⱼ`. -/
noncomputable def crossRelation (a : R) (m : ℕ) (i j : Fin m) :
    Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m :=
  Pi.single i (congruenceX a m j) + Pi.single j (congruenceX a m i)

theorem sqRelation_mem (i : Fin m) : sqRelation a m i ∈ kaehlerRelationSet a m := Or.inl ⟨i, rfl⟩

theorem crossRelation_mem {i j : Fin m} (hij : i ≠ j) :
    crossRelation a m i j ∈ kaehlerRelationSet a m := Or.inr ⟨i, j, hij, rfl⟩

theorem congruenceX_smul_sqRelation_self (i : Fin m) :
    congruenceX a m i • sqRelation a m i
      = a • (Pi.single i (congruenceX a m i)
          : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) := by
  rw [sqRelation, smul_single, aSmul_single]
  congr 1
  rw [mul_sub, mul_add, congruenceX_sq]
  ring

theorem congruenceX_smul_sqRelation_ne {i l : Fin m} (h : l ≠ i) :
    congruenceX a m l • sqRelation a m i
      = -(a • (Pi.single i (congruenceX a m l)
          : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) := by
  rw [sqRelation, smul_single, aSmul_single, ← Pi.single_neg]
  congr 1
  rw [mul_sub, mul_add, congruenceX_mul_of_ne h]
  ring

theorem congruenceX_smul_crossRelation_left {i j : Fin m} (hij : i ≠ j) :
    congruenceX a m i • crossRelation a m i j
      = a • (Pi.single j (congruenceX a m i)
          : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) := by
  rw [crossRelation, smul_add, smul_single, smul_single, aSmul_single,
    congruenceX_mul_of_ne hij, Pi.single_zero, zero_add, congruenceX_sq]

theorem congruenceX_smul_crossRelation_right {i j : Fin m} (hij : i ≠ j) :
    congruenceX a m j • crossRelation a m i j
      = a • (Pi.single i (congruenceX a m j)
          : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) := by
  rw [crossRelation, smul_add, smul_single, smul_single, aSmul_single,
    congruenceX_mul_of_ne hij.symm, Pi.single_zero, add_zero, congruenceX_sq]

theorem congruenceX_smul_crossRelation_other {i j l : Fin m} (hli : l ≠ i) (hlj : l ≠ j) :
    congruenceX a m l • crossRelation a m i j = 0 := by
  rw [crossRelation, smul_add, smul_single, smul_single, congruenceX_mul_of_ne hlj,
    congruenceX_mul_of_ne hli, Pi.single_zero, Pi.single_zero, add_zero]

theorem congruenceX_smul_aSingle_self (i k : Fin m) :
    congruenceX a m k • (a • (Pi.single i (congruenceX a m k)
        : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m))
      = a • (a • (Pi.single i (congruenceX a m k)
          : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) := by
  rw [aSmul_single, ← IsScalarTower.algebraMap_smul
      (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a, smul_single, smul_single]
  congr 1
  rw [← mul_assoc, mul_comm (congruenceX a m k)
      (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a), mul_assoc, congruenceX_sq]

theorem congruenceX_smul_aSingle_ne {k l : Fin m} (h : l ≠ k) (i : Fin m) :
    congruenceX a m l • (a • (Pi.single i (congruenceX a m k)
        : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) = 0 := by
  rw [aSmul_single, smul_single, ← mul_assoc, mul_comm (congruenceX a m l)
      (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a), mul_assoc,
    congruenceX_mul_of_ne h, mul_zero, Pi.single_zero]

/-- The `R`-generators of the relation submodule: the differentiated relations together with the
products `a·xₖ·eᵢ` that they force. -/
noncomputable def kaehlerRelationSetR (a : R) (m : ℕ) :
    Set (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :=
  kaehlerRelationSet a m ∪
    {v | ∃ i k : Fin m, v = a • (Pi.single i (congruenceX a m k)
      : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)}

/-- The relation submodule, viewed over the base ring. -/
noncomputable def kaehlerRelationsR (a : R) (m : ℕ) :
    Submodule R (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :=
  Submodule.span R (kaehlerRelationSetR a m)

theorem aSingle_mem_kaehlerRelations (i k : Fin m) :
    a • (Pi.single i (congruenceX a m k)
        : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ∈ kaehlerRelations a m := by
  by_cases h : k = i
  · subst h
    rw [← congruenceX_smul_sqRelation_self]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (sqRelation_mem k))
  · have hv : congruenceX a m k • sqRelation a m i ∈ kaehlerRelations a m :=
      Submodule.smul_mem _ _ (Submodule.subset_span (sqRelation_mem i))
    rw [congruenceX_smul_sqRelation_ne h] at hv
    simpa using neg_mem hv

theorem congruenceX_smul_mem_relR (l : Fin m)
    {v : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m}
    (hv : v ∈ kaehlerRelationsR a m) :
    congruenceX a m l • v ∈ kaehlerRelationsR a m := by
  classical
  rw [kaehlerRelationsR] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem w hw =>
    rcases hw with (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩) | ⟨i, k, rfl⟩
    · by_cases h : l = i
      · subst h
        show congruenceX a m l • sqRelation a m l ∈ _
        rw [congruenceX_smul_sqRelation_self]
        exact Submodule.subset_span (Or.inr ⟨l, l, rfl⟩)
      · show congruenceX a m l • sqRelation a m i ∈ _
        rw [congruenceX_smul_sqRelation_ne h]
        exact neg_mem (Submodule.subset_span (Or.inr ⟨i, l, rfl⟩))
    · by_cases h1 : l = i
      · subst h1
        show congruenceX a m l • crossRelation a m l j ∈ _
        rw [congruenceX_smul_crossRelation_left hij]
        exact Submodule.subset_span (Or.inr ⟨j, l, rfl⟩)
      · by_cases h2 : l = j
        · subst h2
          show congruenceX a m l • crossRelation a m i l ∈ _
          rw [congruenceX_smul_crossRelation_right hij]
          exact Submodule.subset_span (Or.inr ⟨i, l, rfl⟩)
        · show congruenceX a m l • crossRelation a m i j ∈ _
          rw [congruenceX_smul_crossRelation_other h1 h2]
          exact zero_mem _
    · by_cases h : l = k
      · subst h
        rw [congruenceX_smul_aSingle_self]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, l, rfl⟩))
      · rw [congruenceX_smul_aSingle_ne h]
        exact zero_mem _
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r x,
      smul_smul, mul_comm, ← smul_smul, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ r hx

variable [IsDomain R]

theorem congruenceCoordEquiv_eq (ha : a ≠ 0) (p : R × (Fin m → R)) :
    congruenceCoordEquiv (a := a) (m := m) ha p
      = algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) p.1
        + ∑ k, algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (p.2 k)
            * congruenceX a m k := by
  have hsum : (∑ k, Ideal.Quotient.mk (congruenceIdeal a m) (C (p.2 k) * X k))
      = ∑ k, algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (p.2 k)
          * congruenceX a m k :=
    Finset.sum_congr rfl fun k _ => map_mul _ _ _
  rw [congruenceCoordEquiv_apply, linForm, map_add, map_sum, hsum]
  rfl

theorem smul_mem_relR (ha : a ≠ 0) (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
    {v : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m}
    (hv : v ∈ kaehlerRelationsR a m) : c • v ∈ kaehlerRelationsR a m := by
  obtain ⟨p, rfl⟩ := (congruenceCoordEquiv (a := a) (m := m) ha).surjective c
  rw [congruenceCoordEquiv_eq, add_smul, Finset.sum_smul]
  refine add_mem ?_ (sum_mem fun k _ => ?_)
  · rw [IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ _ hv
  · rw [mul_smul, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ _ (congruenceX_smul_mem_relR k hv)

/-- The `R`-span of the enlarged generating set, promoted to a submodule over the order. -/
noncomputable def kaehlerRelationsA (ha : a ≠ 0) :
    Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) where
  carrier := (kaehlerRelationsR a m : Set (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m))
  add_mem' hx hy := add_mem hx hy
  zero_mem' := zero_mem _
  smul_mem' c _ hv := smul_mem_relR ha c hv

/-- The relation submodule is the `R`-span of the differentiated relations together with the
elements `a·xₖ·eᵢ`. -/
theorem kaehlerRelations_restrictScalars (ha : a ≠ 0) :
    (kaehlerRelations a m).restrictScalars R = kaehlerRelationsR a m := by
  refine le_antisymm (fun v hv => ?_) ?_
  · have hsub : kaehlerRelationSet a m
        ⊆ (kaehlerRelationsA (a := a) (m := m) ha : Set _) := by
      rintro w (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩)
      · exact Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩))
      · exact Submodule.subset_span (Or.inl (Or.inr ⟨i, j, hij, rfl⟩))
    exact (Submodule.span_le.2 hsub) hv
  · rw [kaehlerRelationsR, Submodule.span_le]
    rintro w ((⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩) | ⟨i, k, rfl⟩)
    · exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    · exact Submodule.subset_span (Or.inr ⟨i, j, hij, rfl⟩)
    · exact aSingle_mem_kaehlerRelations i k

end Relations

/-! ## The cotangent module is the diagonal-plus-antisymmetric model -/

section Model

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [IsDomain R]

theorem congruenceCoordEquiv_symm_algebraMap (ha : a ≠ 0) (r : R) :
    (congruenceCoordEquiv (a := a) (m := m) ha).symm
        (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r) = (r, 0) := by
  rw [LinearEquiv.symm_apply_eq, congruenceCoordEquiv_apply]
  have h : linForm r (0 : Fin m → R) = C r := by simp [linForm]
  rw [h]
  rfl

theorem congruenceCoordEquiv_symm_sqGen (ha : a ≠ 0) (i : Fin m) :
    (congruenceCoordEquiv (a := a) (m := m) ha).symm
        (congruenceX a m i + congruenceX a m i
          - algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a)
      = (-a, Pi.single i 1 + Pi.single i 1) := by
  rw [map_sub, map_add, congruenceCoordEquiv_symm_gen, congruenceCoordEquiv_symm_algebraMap]
  refine Prod.ext ?_ ?_ <;> simp

variable [Invertible (2 : R)]

theorem kaehlerSplitRaw_sqRelation (ha : a ≠ 0) (i : Fin m) :
    kaehlerSplitRaw ha (sqRelation a m i) = 0 := by
  classical
  refine Prod.ext (funext fun j => ?_) (funext fun p => ?_)
  · rw [sqRelation, kaehlerSplitRaw_single_fst, congruenceCoordEquiv_symm_sqGen]
    by_cases h : j = i
    · subst h
      rw [if_pos rfl]
      have hcalc : (-a) + ⅟(2 : R) * a * ((Pi.single j (1 : R) : Fin m → R) j
          + (Pi.single j (1 : R) : Fin m → R) j) = 0 := by
        rw [Pi.single_eq_same]
        have h2 : (1 : R) + 1 = 2 := by norm_num
        rw [h2]
        calc (-a) + ⅟(2 : R) * a * 2 = (-a) + (⅟(2 : R) * 2) * a := by ring
          _ = (-a) + a := by rw [invOf_mul_self, one_mul]
          _ = 0 := by ring
      show Submodule.Quotient.mk ((-a) + ⅟(2 : R) * a * ((Pi.single j (1 : R) : Fin m → R) j
        + (Pi.single j (1 : R) : Fin m → R) j)) = 0
      rw [hcalc]
      simp
    · rw [if_neg h]
      rfl
  · rw [sqRelation, kaehlerSplitRaw_single_snd, congruenceCoordEquiv_symm_sqGen]
    have hlt : p.1.1 < p.1.2 := p.2
    have key : ∀ l : Fin m, l ≠ i →
        ((-a, (Pi.single i (1 : R) + Pi.single i (1 : R) : Fin m → R)) : R × (Fin m → R)).2 l
          = 0 := by
      intro l hl
      show (Pi.single i (1 : R) : Fin m → R) l + (Pi.single i (1 : R) : Fin m → R) l = 0
      rw [Pi.single_eq_of_ne hl]
      simp
    by_cases h1 : p.1.1 = i
    · have h2 : p.1.2 ≠ i := by
        intro hc
        rw [h1, hc] at hlt
        exact lt_irrefl _ hlt
      rw [if_pos h1, if_neg h2, key _ h2, sub_zero]
      simp
    · rw [if_neg h1]
      by_cases h2 : p.1.2 = i
      · rw [if_pos h2, key _ h1, zero_sub, neg_zero]
        simp
      · rw [if_neg h2, sub_zero]
        simp

theorem kaehlerSplitRaw_crossRelation (ha : a ≠ 0) {i j : Fin m} (hij : i ≠ j) :
    kaehlerSplitRaw ha (crossRelation a m i j) = 0 := by
  rw [crossRelation, map_add]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [kaehlerSplitRaw_single_lt ha h, kaehlerSplitRaw_single_gt ha h]
    simp
  · rw [kaehlerSplitRaw_single_gt ha h, kaehlerSplitRaw_single_lt ha h]
    simp

theorem kaehlerSplitRaw_aSingle (ha : a ≠ 0) (i k : Fin m) :
    kaehlerSplitRaw ha (a • (Pi.single i (congruenceX a m k)
      : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) = 0 := by
  classical
  have hza : (Submodule.Quotient.mk a : R ⧸ Ideal.span ({a} : Set R)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 dvd_rfl)
  rw [map_smul]
  rcases lt_trichotomy i k with h | h | h
  · rw [kaehlerSplitRaw_single_lt ha h]
    refine Prod.ext (by simp) ?_
    show a • (Pi.single (ι := pairIndex m) (M := fun _ => R ⧸ Ideal.span ({a} : Set R))
      ⟨(i, k), h⟩ (Submodule.Quotient.mk 1)) = 0
    rw [← Pi.single_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, hza,
      Pi.single_zero]
  · subst h
    rw [kaehlerSplitRaw_single_self ha i]
    have hz : (Submodule.Quotient.mk (a * (⅟(2 : R) * a))
        : R ⧸ Ideal.span ({a ^ 2} : Set R)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ⟨⅟(2 : R), by ring⟩)
    refine Prod.ext ?_ (by simp)
    show a • (Pi.single (ι := Fin m) (M := fun _ => R ⧸ Ideal.span ({a ^ 2} : Set R))
      i (Submodule.Quotient.mk (⅟(2 : R) * a))) = 0
    rw [← Pi.single_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, hz, Pi.single_zero]
  · rw [kaehlerSplitRaw_single_gt ha h]
    refine Prod.ext (by simp) ?_
    show a • (-(Pi.single (ι := pairIndex m) (M := fun _ => R ⧸ Ideal.span ({a} : Set R))
      ⟨(k, i), h⟩ (Submodule.Quotient.mk 1))) = 0
    rw [smul_neg, ← Pi.single_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, hza,
      Pi.single_zero, neg_zero]

theorem kaehlerRelationsR_le_ker (ha : a ≠ 0) :
    kaehlerRelationsR a m ≤ LinearMap.ker (kaehlerSplitRaw ha) := by
  rw [kaehlerRelationsR, Submodule.span_le]
  rintro w ((⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩) | ⟨i, k, rfl⟩)
  · exact kaehlerSplitRaw_sqRelation ha i
  · exact kaehlerSplitRaw_crossRelation ha hij
  · exact kaehlerSplitRaw_aSingle ha i k

/-- The splitting map descends to the cotangent model. -/
noncomputable def kaehlerSplit (ha : a ≠ 0) :
    ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)
      →ₗ[R] cotangentModel a m :=
  Submodule.liftQ ((kaehlerRelations a m).restrictScalars R) (kaehlerSplitRaw ha)
    (by rw [kaehlerRelations_restrictScalars ha]; exact kaehlerRelationsR_le_ker ha)

theorem kaehlerSplit_mk (ha : a ≠ 0)
    (v : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :
    kaehlerSplit ha (Submodule.Quotient.mk v) = kaehlerSplitRaw ha v := rfl

end Model

/-! ## The inverse of the splitting map -/

section Inverse

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

theorem rSmul_single_one (r : R) (i : Fin m) :
    r • (Pi.single i (1 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      = Pi.single i (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r) := by
  rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r,
    smul_single, mul_one]

theorem rSmul_single_gen (r : R) (i k : Fin m) :
    r • (Pi.single i (congruenceX a m k)
        : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      = Pi.single i (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r
          * congruenceX a m k) := by
  rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r,
    smul_single]

theorem single_sum {ι : Type*} (s : Finset ι) (i : Fin m)
    (f : ι → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :
    (Pi.single i (∑ k ∈ s, f k) : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      = ∑ k ∈ s, Pi.single i (f k) := by
  classical
  have h := map_sum (LinearMap.single R
    (fun _ : Fin m => MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) i) f s
  simpa only [LinearMap.coe_single] using h

/-- The class of `eᵢ` in the cotangent module. -/
noncomputable def cotBasis (a : R) (m : ℕ) (i : Fin m) :
    (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m :=
  Submodule.Quotient.mk (Pi.single i 1)

/-- The class of `xₖ·eᵢ` in the cotangent module. -/
noncomputable def cotPair (a : R) (m : ℕ) (i k : Fin m) :
    (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m :=
  Submodule.Quotient.mk (Pi.single i (congruenceX a m k))

theorem smul_a_cotPair (i k : Fin m) : a • cotPair a m i k = 0 := by
  rw [cotPair, ← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).2 (aSingle_mem_kaehlerRelations i k)

theorem cotPair_self_add (i : Fin m) :
    cotPair a m i i + cotPair a m i i = a • cotBasis a m i := by
  have hs : sqRelation a m i
      = Pi.single i (congruenceX a m i) + Pi.single i (congruenceX a m i)
        - a • (Pi.single i (1 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
            : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) := by
    rw [rSmul_single_one, sqRelation, ← Pi.single_add, ← Pi.single_sub]
  have h0 : (Submodule.Quotient.mk (sqRelation a m i)
      : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (sqRelation_mem i))
  rw [hs, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
    sub_eq_zero] at h0
  exact h0

theorem cotPair_swap {i j : Fin m} (hij : i ≠ j) :
    cotPair a m i j = -cotPair a m j i := by
  have h0 : (Submodule.Quotient.mk (crossRelation a m i j)
      : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (crossRelation_mem hij))
  rw [crossRelation, Submodule.Quotient.mk_add] at h0
  exact add_eq_zero_iff_eq_neg.1 h0

theorem sq_smul_cotBasis (i : Fin m) : (a ^ 2) • cotBasis a m i = 0 := by
  calc (a ^ 2) • cotBasis a m i = a • (a • cotBasis a m i) := by rw [pow_two, mul_smul]
    _ = a • (cotPair a m i i + cotPair a m i i) := by rw [cotPair_self_add]
    _ = a • cotPair a m i i + a • cotPair a m i i := by rw [smul_add]
    _ = 0 := by rw [smul_a_cotPair, add_zero]

theorem cotPair_self [Invertible (2 : R)] (i : Fin m) :
    cotPair a m i i = (⅟(2 : R) * a) • cotBasis a m i := by
  have h : (2 : R) • cotPair a m i i = a • cotBasis a m i := by
    rw [two_smul]
    exact cotPair_self_add i
  calc cotPair a m i i = (⅟(2 : R) * 2) • cotPair a m i i := by rw [invOf_mul_self, one_smul]
    _ = ⅟(2 : R) • ((2 : R) • cotPair a m i i) := by rw [mul_smul]
    _ = ⅟(2 : R) • (a • cotBasis a m i) := by rw [h]
    _ = (⅟(2 : R) * a) • cotBasis a m i := by rw [mul_smul]

/-- The diagonal sector maps into the cotangent module by `r ↦ r·eᵢ`. -/
noncomputable def diagLift (i : Fin m) :
    (R ⧸ Ideal.span ({a ^ 2} : Set R)) →ₗ[R]
      ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :=
  Submodule.liftQ (Ideal.span ({a ^ 2} : Set R))
    (LinearMap.toSpanSingleton R _ (cotBasis a m i))
    (by
      refine Submodule.span_le.2 ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact sq_smul_cotBasis i)

/-- The antisymmetric sector maps into the cotangent module by `r ↦ r·xⱼdxᵢ`. -/
noncomputable def pairLift (p : pairIndex m) :
    (R ⧸ Ideal.span ({a} : Set R)) →ₗ[R]
      ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :=
  Submodule.liftQ (Ideal.span ({a} : Set R))
    (LinearMap.toSpanSingleton R _ (cotPair a m p.1.1 p.1.2))
    (by
      refine Submodule.span_le.2 ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact smul_a_cotPair p.1.1 p.1.2)

theorem diagLift_mk (i : Fin m) (r : R) :
    diagLift (a := a) i (Submodule.Quotient.mk r) = r • cotBasis a m i := rfl

theorem pairLift_mk (p : pairIndex m) (r : R) :
    pairLift (a := a) p (Submodule.Quotient.mk r) = r • cotPair a m p.1.1 p.1.2 := rfl

/-- The inverse comparison map from the diagonal-plus-antisymmetric model. -/
noncomputable def modelInv :
    cotangentModel a m →ₗ[R]
      ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :=
  (∑ i : Fin m, (diagLift (a := a) i).comp
      ((LinearMap.proj i).comp (LinearMap.fst R _ _)))
    + ∑ p : pairIndex m, (pairLift (a := a) p).comp
      ((LinearMap.proj p).comp (LinearMap.snd R _ _))

theorem modelInv_mk (u : Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R))
    (w : pairIndex m → R ⧸ Ideal.span ({a} : Set R)) :
    modelInv (a := a) (m := m) (u, w)
      = (∑ i, diagLift i (u i)) + ∑ p, pairLift p (w p) := by
  simp [modelInv]

theorem modelInv_diag (i : Fin m) (t : R ⧸ Ideal.span ({a ^ 2} : Set R)) :
    modelInv (a := a) (m := m) (Pi.single i t, 0) = diagLift i t := by
  classical
  rw [modelInv_mk, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  simp

theorem modelInv_pair (p : pairIndex m) (t : R ⧸ Ideal.span ({a} : Set R)) :
    modelInv (a := a) (m := m) (0, Pi.single p t) = pairLift p t := by
  classical
  rw [modelInv_mk, Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq, map_zero])
    (fun h => absurd (Finset.mem_univ p) h), Pi.single_eq_same]
  simp

theorem modelInv_pair_neg (p : pairIndex m) (t : R ⧸ Ideal.span ({a} : Set R)) :
    modelInv (a := a) (m := m) (0, -Pi.single p t) = -pairLift p t := by
  have h : (((0 : Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)),
        -Pi.single p t) : cotangentModel a m)
      = -(((0 : Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)),
        Pi.single p t) : cotangentModel a m) := by
    rw [Prod.neg_mk, neg_zero]
  rw [h, map_neg, modelInv_pair]

/-- The generating set of the cotangent module over `R`. -/
noncomputable def cotGens (a : R) (m : ℕ) :
    Set ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :=
  {q | ∃ i, q = cotBasis a m i} ∪ {q | ∃ i k, q = cotPair a m i k}

end Inverse

/-! ## The cotangent module of the congruence order -/

section Equiv

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [IsDomain R]

theorem span_cotGens (ha : a ≠ 0) : Submodule.span R (cotGens a m) = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (kaehlerRelations a m) x
  have key : ∀ (i : Fin m) (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m),
      (Submodule.Quotient.mk (Pi.single i c)
        : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)
        ∈ Submodule.span R (cotGens a m) := by
    intro i c
    obtain ⟨q, rfl⟩ := (congruenceCoordEquiv (a := a) (m := m) ha).surjective c
    rw [congruenceCoordEquiv_eq]
    have hsingle : (Pi.single i (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) q.1
          + ∑ k, algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (q.2 k)
              * congruenceX a m k)
        : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        = q.1 • (Pi.single i (1 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
            : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
          + ∑ k, q.2 k • (Pi.single i (congruenceX a m k)
            : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) := by
      rw [rSmul_single_one, Finset.sum_congr rfl (fun k _ => rSmul_single_gen (q.2 k) i k),
        Pi.single_add, single_sum]
    rw [hsingle, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]
    refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩))) ?_
    have hsum : (Submodule.Quotient.mk (∑ k, q.2 k • Pi.single i (congruenceX a m k))
        : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)
        = ∑ k, q.2 k • cotPair a m i k := by
      show (kaehlerRelations a m).mkQ (∑ k, q.2 k • Pi.single i (congruenceX a m k)) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
        rfl
    rw [hsum]
    exact sum_mem fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, k, rfl⟩))
  have hv : (Submodule.Quotient.mk v
      : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)
      = ∑ i, Submodule.Quotient.mk (Pi.single i (v i)) := by
    have hmap := map_sum ((kaehlerRelations a m).mkQ) (fun i => Pi.single i (v i)) Finset.univ
    rw [Finset.univ_sum_single] at hmap
    exact hmap
  rw [hv]
  exact sum_mem fun i _ => key i (v i)

variable [Invertible (2 : R)]

theorem kaehlerSplit_diagLift (ha : a ≠ 0) (i : Fin m)
    (t : R ⧸ Ideal.span ({a ^ 2} : Set R)) :
    kaehlerSplit ha (diagLift i t) = (Pi.single i t, 0) := by
  classical
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span ({a ^ 2} : Set R)) t
  rw [diagLift_mk, cotBasis, ← Submodule.Quotient.mk_smul, kaehlerSplit_mk, map_smul,
    kaehlerSplitRaw_single_one]
  refine Prod.ext ?_ (by simp)
  show r • (Pi.single (ι := Fin m) (M := fun _ => R ⧸ Ideal.span ({a ^ 2} : Set R)) i
    (Submodule.Quotient.mk 1)) = Pi.single i (Submodule.Quotient.mk r)
  rw [← Pi.single_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

theorem kaehlerSplit_pairLift (ha : a ≠ 0) (p : pairIndex m)
    (t : R ⧸ Ideal.span ({a} : Set R)) :
    kaehlerSplit ha (pairLift p t) = (0, Pi.single p t) := by
  classical
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span ({a} : Set R)) t
  rw [pairLift_mk, cotPair, ← Submodule.Quotient.mk_smul, kaehlerSplit_mk, map_smul,
    kaehlerSplitRaw_single_lt ha p.2]
  refine Prod.ext (by simp) ?_
  show r • (Pi.single (ι := pairIndex m) (M := fun _ => R ⧸ Ideal.span ({a} : Set R))
    ⟨(p.1.1, p.1.2), p.2⟩ (Submodule.Quotient.mk 1)) = Pi.single p (Submodule.Quotient.mk r)
  rw [← Pi.single_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

theorem kaehlerSplit_modelInv (ha : a ≠ 0) (u : cotangentModel a m) :
    kaehlerSplit ha (modelInv u) = u := by
  classical
  obtain ⟨u1, u2⟩ := u
  rw [modelInv_mk, map_add, map_sum, map_sum,
    Finset.sum_congr rfl (fun i _ => kaehlerSplit_diagLift ha i (u1 i)),
    Finset.sum_congr rfl (fun p _ => kaehlerSplit_pairLift ha p (u2 p))]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, Prod.fst_sum, Prod.fst_sum]
    simp [Finset.univ_sum_single]
  · rw [Prod.snd_add, Prod.snd_sum, Prod.snd_sum]
    simp [Finset.univ_sum_single]

theorem modelInv_kaehlerSplit (ha : a ≠ 0)
    (x : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m) :
    modelInv (kaehlerSplit ha x) = x := by
  classical
  have hfun : (modelInv (a := a) (m := m)).comp (kaehlerSplit ha) = LinearMap.id := by
    refine LinearMap.ext_on (span_cotGens ha) ?_
    rintro q (⟨i, rfl⟩ | ⟨i, k, rfl⟩)
    · show modelInv (kaehlerSplit ha (cotBasis a m i)) = cotBasis a m i
      rw [cotBasis, kaehlerSplit_mk, kaehlerSplitRaw_single_one, modelInv_diag, diagLift_mk,
        one_smul]
      rfl
    · show modelInv (kaehlerSplit ha (cotPair a m i k)) = cotPair a m i k
      rw [cotPair, kaehlerSplit_mk]
      rcases lt_trichotomy i k with h | h | h
      · rw [kaehlerSplitRaw_single_lt ha h, modelInv_pair, pairLift_mk, one_smul]
        rfl
      · subst h
        rw [kaehlerSplitRaw_single_self ha i, modelInv_diag, diagLift_mk, ← cotPair_self]
        rfl
      · rw [kaehlerSplitRaw_single_gt ha h, modelInv_pair_neg, pairLift_mk, one_smul,
          ← cotPair_swap h.ne']
        rfl
  exact congrArg (fun f => f x) hfun

/-- **Card `(5)`, model form.**  The cotangent model of the diagonal congruence order splits as a
diagonal sector `(R/a²)^m` and an antisymmetric sector `(R/a)^{binom m 2}`. -/
noncomputable def cotangentModelEquiv (ha : a ≠ 0) :
    ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)
      ≃ₗ[R] cotangentModel a m :=
  LinearEquiv.ofLinear (kaehlerSplit ha) modelInv
    (LinearMap.ext (kaehlerSplit_modelInv ha)) (LinearMap.ext (modelInv_kaehlerSplit ha))

/-- **Card `(5)`.**  `Ω_{A/R} ≅ (R/a²)^m ⊕ (R/a)^{binom m 2}` for the diagonal congruence order
`A = R·1 + a·R^{m+1}`. -/
noncomputable def kaehlerCongruenceEquiv (ha : a ≠ 0) :
    Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] ≃ₗ[R] cotangentModel a m :=
  (LinearEquiv.restrictScalars R (kaehlerModelEquiv (a := a) (m := m))).trans
    (cotangentModelEquiv ha)

end Equiv

end HTGeometry.ConstraintRelativity
