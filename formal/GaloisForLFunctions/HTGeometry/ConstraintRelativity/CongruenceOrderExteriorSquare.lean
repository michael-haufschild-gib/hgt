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

end HTGeometry.ConstraintRelativity
