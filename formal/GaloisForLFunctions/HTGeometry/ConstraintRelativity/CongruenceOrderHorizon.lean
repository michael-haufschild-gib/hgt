import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CongruenceOrderTraceDual

/-!
# Barcode invariants of the diagonal congruence order

The antisymmetric cotangent sector of the diagonal congruence order is indexed by the ordered
pairs of sheets, hence has rank `binom (N-1) 2`, and the trace-law and cotangent-law lengths
differ by exactly that number.
-/

namespace HTGeometry.ConstraintRelativity

/-! ## The antisymmetric index set -/

section PairIndex

variable {m : ℕ}

/-- The two-element subset attached to an ordered pair of sheets. -/
def pairToFinset (p : pairIndex m) : Set.powersetCard (Fin m) 2 :=
  ⟨{p.1.1, p.1.2}, by
    classical
    show ({p.1.1, p.1.2} : Finset (Fin m)).card = 2
    rw [Finset.card_insert_of_notMem (by simp [p.2.ne]), Finset.card_singleton]⟩

theorem pairToFinset_coe (p : pairIndex m) :
    (pairToFinset p : Finset (Fin m)) = {p.1.1, p.1.2} := rfl

theorem pairToFinset_injective : Function.Injective (pairToFinset (m := m)) := by
  classical
  intro p q h
  have h' : ({p.1.1, p.1.2} : Finset (Fin m)) = {q.1.1, q.1.2} := congrArg Subtype.val h
  have hp1 : p.1.1 ∈ ({q.1.1, q.1.2} : Finset (Fin m)) := by rw [← h']; simp
  have hp2 : p.1.2 ∈ ({q.1.1, q.1.2} : Finset (Fin m)) := by rw [← h']; simp
  have hq2 : q.1.2 ∈ ({p.1.1, p.1.2} : Finset (Fin m)) := by rw [h']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2 hq2
  have hpl : (p.1.1 : ℕ) < p.1.2 := p.2
  have hql : (q.1.1 : ℕ) < q.1.2 := q.2
  rw [Fin.ext_iff] at hp1 hp2 hq2
  refine Subtype.ext (Prod.ext ?_ ?_) <;> rw [Fin.ext_iff] <;> omega

theorem pairToFinset_surjective : Function.Surjective (pairToFinset (m := m)) := by
  classical
  rintro ⟨s, hs⟩
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨⟨(x, y), h⟩, rfl⟩
  · exact ⟨⟨(y, x), h⟩, Subtype.ext (Finset.pair_comm y x)⟩

/-- Ordered pairs of sheets are the same as two-element sets of sheets. -/
noncomputable def pairIndexEquivPowersetCard (m : ℕ) :
    pairIndex m ≃ Set.powersetCard (Fin m) 2 :=
  Equiv.ofBijective _ ⟨pairToFinset_injective, pairToFinset_surjective⟩

/-- **Card `(7)`.**  The antisymmetric cotangent sector has rank `binom (N−1) 2`. -/
theorem card_pairIndex (m : ℕ) : Fintype.card (pairIndex m) = m.choose 2 := by
  classical
  rw [Fintype.card_congr (pairIndexEquivPowersetCard m)]
  have h : Fintype.card {s : Finset (Fin m) // s.card = 2} = (Fintype.card (Fin m)).choose 2 :=
    Fintype.card_finset_len 2
  rw [Fintype.card_fin] at h
  exact h.symm ▸ Fintype.card_congr (Equiv.refl _)

end PairIndex

/-! ## Lengths of the two defect modules -/

section Lengths

variable {R : Type*} [CommRing R]

theorem length_quotient_span_of_isMaximal (a : R)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (R ⧸ Ideal.span ({a} : Set R)) = 1 :=
  Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 hmax.out)

theorem length_quotient_span_sq [IsDomain R] {a : R} (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (R ⧸ Ideal.span ({a ^ 2} : Set R)) = 2 := by
  have hord : Ring.ord R (a * a) = Ring.ord R a + Ring.ord R a :=
    Ring.ord_mul R (mem_nonZeroDivisors_of_ne_zero ha)
  have hone : Ring.ord R a = 1 := length_quotient_span_of_isMaximal a hmax
  show Ring.ord R (a ^ 2) = 2
  rw [pow_two, hord, hone]
  rfl

variable {a : R} {m : ℕ}

theorem length_traceDefectModel [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) = ((2 * m : ℕ) : ℕ∞) := by
  rw [Module.length_pi_of_fintype,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => length_quotient_span_sq ha hmax),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem length_pairSector (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (pairIndex m → R ⧸ Ideal.span ({a} : Set R))
      = ((m.choose 2 : ℕ) : ℕ∞) := by
  classical
  rw [Module.length_pi_of_fintype,
    Finset.sum_congr rfl
      (fun p (_ : p ∈ Finset.univ) => length_quotient_span_of_isMaximal a hmax),
    Finset.sum_const, Finset.card_univ, card_pairIndex, nsmul_eq_mul, mul_one]

/-- **Card `(27)`.**  The cotangent-law defect has length `2m + binom m 2`. -/
theorem length_cotangentModel [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (cotangentModel a m) = ((2 * m + m.choose 2 : ℕ) : ℕ∞) := by
  show Module.length R ((Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) ×
    (pairIndex m → R ⧸ Ideal.span ({a} : Set R))) = _
  rw [Module.length_prod, length_traceDefectModel ha hmax, length_pairSector hmax]
  push_cast
  ring

/-- **Card `(28)`.**  The cotangent-law length exceeds the trace-law length by exactly
`binom (N−1) 2`. -/
theorem length_cotangentModel_eq_length_traceDefect_add [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (cotangentModel a m)
      = Module.length R (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) + ((m.choose 2 : ℕ) : ℕ∞) := by
  rw [length_cotangentModel ha hmax, length_traceDefectModel ha hmax]
  push_cast
  ring

end Lengths

/-! ## The closed horizon fibre -/

section Fibre

variable {R : Type*} [CommRing R]

/-- The submodule `a·M` of multiples of `a`. -/
def aMul (a : R) (M : Type*) [AddCommGroup M] [Module R M] : Submodule R M :=
  LinearMap.range (a • LinearMap.id : M →ₗ[R] M)

theorem mem_aMul {a : R} {M : Type*} [AddCommGroup M] [Module R M] {x : M} :
    x ∈ aMul a M ↔ ∃ u : M, a • u = x := Iff.rfl

theorem map_aMul {a : R} {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (e : M ≃ₗ[R] N) : Submodule.map (e : M →ₗ[R] N) (aMul a M) = aMul a N := by
  ext y
  simp only [Submodule.mem_map, mem_aMul]
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨e u, by rw [LinearEquiv.coe_coe, map_smul]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨a • e.symm u, ⟨e.symm u, rfl⟩,
      by rw [LinearEquiv.coe_coe, map_smul, e.apply_symm_apply]⟩

theorem aMul_prod (a : R) (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] : aMul a (M × N) = (aMul a M).prod (aMul a N) := by
  ext x
  rw [Submodule.mem_prod]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨⟨u.1, rfl⟩, ⟨u.2, rfl⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨(u, v), Prod.ext hu hv⟩

theorem aMul_pi (a : R) {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] :
    aMul a (∀ i, M i) = Submodule.pi Set.univ fun i => aMul a (M i) := by
  ext x
  rw [Submodule.mem_pi]
  constructor
  · rintro ⟨u, rfl⟩ i _
    exact ⟨u i, rfl⟩
  · intro h
    choose u hu using fun i => h i (Set.mem_univ i)
    exact ⟨u, funext hu⟩

theorem aMul_quotient_span_eq_bot (a : R) :
    aMul a (R ⧸ Ideal.span ({a} : Set R)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_aMul] at hx
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span ({a} : Set R)) u
  rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mem_span_singleton.2 ⟨s, rfl⟩

/-- The composite `R → R/a² → (R/a²)/(a·)`. -/
noncomputable def sqFibreMap (a : R) :
    R →ₗ[R] ((R ⧸ Ideal.span ({a ^ 2} : Set R)) ⧸ aMul a (R ⧸ Ideal.span ({a ^ 2} : Set R))) :=
  (aMul a (R ⧸ Ideal.span ({a ^ 2} : Set R))).mkQ.comp (Ideal.span ({a ^ 2} : Set R)).mkQ

theorem sqFibreMap_surjective (a : R) : Function.Surjective (sqFibreMap a) :=
  (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)

theorem ker_sqFibreMap (a : R) :
    LinearMap.ker (sqFibreMap a) = Ideal.span ({a} : Set R) := by
  ext r
  rw [LinearMap.mem_ker, sqFibreMap, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_aMul, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span ({a ^ 2} : Set R)) u
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.eq,
      Ideal.mem_span_singleton] at hu
    obtain ⟨w, hw⟩ := hu
    exact ⟨s - a * w, by linear_combination -hw⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Submodule.Quotient.mk t, by rw [← Submodule.Quotient.mk_smul, smul_eq_mul]⟩

/-- `(R/a²)/a(R/a²) ≅ R/a`. -/
noncomputable def sqFibreEquiv (a : R) :
    ((R ⧸ Ideal.span ({a ^ 2} : Set R)) ⧸ aMul a (R ⧸ Ideal.span ({a ^ 2} : Set R)))
      ≃ₗ[R] (R ⧸ Ideal.span ({a} : Set R)) :=
  (LinearMap.quotKerEquivOfSurjective _ (sqFibreMap_surjective a)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_sqFibreMap a))

/-- `(R/a)/a(R/a) ≅ R/a`. -/
noncomputable def linFibreEquiv (a : R) :
    ((R ⧸ Ideal.span ({a} : Set R)) ⧸ aMul a (R ⧸ Ideal.span ({a} : Set R)))
      ≃ₗ[R] (R ⧸ Ideal.span ({a} : Set R)) :=
  Submodule.quotEquivOfEqBot _ (aMul_quotient_span_eq_bot a)

/-- The `a`-fibre of a finite product of modules. -/
noncomputable def piFibreEquiv (a : R) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    ((∀ i, M i) ⧸ aMul a (∀ i, M i)) ≃ₗ[R] ∀ i, (M i ⧸ aMul a (M i)) :=
  (Submodule.quotEquivOfEq _ _ (aMul_pi a M)).trans (Submodule.quotientPi _)

/-- The `a`-fibre of a product of two modules. -/
noncomputable def prodFibreEquiv (a : R) (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    ((M × N) ⧸ aMul a (M × N)) ≃ₗ[R] (M ⧸ aMul a M) × (N ⧸ aMul a N) :=
  (Submodule.quotEquivOfEq _ _
      (by rw [LinearMap.ker_prodMap, Submodule.ker_mkQ, Submodule.ker_mkQ, aMul_prod] :
        aMul a (M × N)
          = LinearMap.ker ((aMul a M).mkQ.prodMap (aMul a N).mkQ))).trans
    (LinearMap.quotKerEquivOfSurjective _
      (Function.Surjective.prodMap (Submodule.mkQ_surjective _) (Submodule.mkQ_surjective _)))

theorem aMul_eq_smul_top (a : R) (M : Type*) [AddCommGroup M] [Module R M] :
    aMul a M = Ideal.span ({a} : Set R) • (⊤ : Submodule R M) := by
  refine le_antisymm ?_ ?_
  · rintro x hx
    rw [mem_aMul] at hx
    obtain ⟨u, rfl⟩ := hx
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton.2 dvd_rfl) Submodule.mem_top
  · refine Submodule.smul_le.2 fun c hc x _ => ?_
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hc
    rw [mem_aMul]
    exact ⟨d • x, by rw [mul_smul]⟩

/-- An `R`-linear equivalence between `R ⧸ I`-modules whose `R`-action factors through `R ⧸ I`
is `R ⧸ I`-linear. -/
def quotientScalarsEquiv (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
    [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] [AddCommGroup N] [Module R N]
    [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] (e : M ≃ₗ[R] N) : M ≃ₗ[R ⧸ I] N where
  toFun := e
  invFun := e.symm
  map_add' := e.map_add
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : ∀ y : M, (Ideal.Quotient.mk I r) • y = r • y := fun y => by
      rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
    have hr' : ∀ y : N, (Ideal.Quotient.mk I r) • y = r • y := fun y => by
      rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
    rw [hr, RingHom.id_apply, hr', map_smul]
  left_inv := e.left_inv
  right_inv := e.right_inv

end Fibre

/-! ## Card (6): the closed-horizon exterior-square law -/

section Horizon

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

/-- The antisymmetric sector is the exterior square of the observer defect. -/
noncomputable def exteriorSquareModel (m : ℕ) (k : Type*) [CommRing k] :
    (pairIndex m → k) ≃ₗ[k] ⋀[k]^2 (Fin m → k) := by
  classical
  letI : Fintype (Set.powersetCard (Fin m) 2) :=
    Fintype.ofEquiv _ (pairIndexEquivPowersetCard m)
  exact (LinearEquiv.piCongrLeft' k (fun _ : pairIndex m => k)
      (pairIndexEquivPowersetCard m)).trans
    (Module.Basis.exteriorPower 2 (Pi.basisFun k (Fin m))).equivFun.symm

/-- The `a`-fibre of the cotangent model splits into the observer sector and the pair sector. -/
noncomputable def cotangentFibreEquiv (a : R) (m : ℕ) :
    (cotangentModel a m ⧸ aMul a (cotangentModel a m))
      ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a} : Set R)) ×
        (pairIndex m → R ⧸ Ideal.span ({a} : Set R)) := by
  classical
  exact (prodFibreEquiv a _ _).trans
    (LinearEquiv.prodCongr
      ((piFibreEquiv a _).trans (LinearEquiv.piCongrRight fun _ => sqFibreEquiv a))
      ((piFibreEquiv a _).trans (LinearEquiv.piCongrRight fun _ => linFibreEquiv a)))

variable [IsDomain R] [Invertible (2 : R)]

/-- The closed-horizon cotangent fibre, split into the observer sector and the pair sector. -/
noncomputable def kaehlerFibreEquiv (ha : a ≠ 0) :
    (Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
        ⧸ (Ideal.span ({a} : Set R) •
          (⊤ : Submodule R Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])))
      ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a} : Set R)) ×
        (pairIndex m → R ⧸ Ideal.span ({a} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ (aMul_eq_smul_top a _).symm).trans
    ((Submodule.Quotient.equiv _ _ (kaehlerCongruenceEquiv ha)
      (map_aMul (kaehlerCongruenceEquiv ha))).trans (cotangentFibreEquiv a m))

/-- **Card `(6)`.**  At the closed horizon the cotangent fibre is the observer defect together
with its exterior square. -/
noncomputable def horizonExteriorSquareEquiv (ha : a ≠ 0) :
    (Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
        ⧸ (Ideal.span ({a} : Set R) •
          (⊤ : Submodule R Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])))
      ≃ₗ[R ⧸ Ideal.span ({a} : Set R)]
        ((Fin m → R ⧸ Ideal.span ({a} : Set R)) ×
          ⋀[R ⧸ Ideal.span ({a} : Set R)]^2 (Fin m → R ⧸ Ideal.span ({a} : Set R))) :=
  (quotientScalarsEquiv (Ideal.span ({a} : Set R)) (kaehlerFibreEquiv ha)).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
      (exteriorSquareModel m (R ⧸ Ideal.span ({a} : Set R))))

/-! ### The three-sheet hostile counterexample -/

section ThreeSheet

variable {R : Type*} [CommRing R] {a : R}

/-- **Card `(29)`.**  At three sheets the antisymmetric cotangent sector is a single copy. -/
theorem card_pairIndex_two : Fintype.card (pairIndex 2) = 1 := card_pairIndex 2

/-- **Card `(29)`.**  Three sheets: the cotangent-law defect has length `5`. -/
theorem length_cotangentModel_two [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (cotangentModel a 2) = (5 : ℕ∞) := by
  rw [length_cotangentModel ha hmax]
  norm_num

/-- **Card `(29)`.**  Three sheets: the trace-law defect has length `4`. -/
theorem length_traceDefectModel_two [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (Fin 2 → R ⧸ Ideal.span ({a ^ 2} : Set R)) = (4 : ℕ∞) := by
  rw [length_traceDefectModel ha hmax]
  norm_num

/-- **Card `(29)`, boxed reading.**  At three sheets the cotangent-law defect and the trace-law
defect are *not isomorphic*, although the Kähler and Dedekind differents agree there: the lengths
are `5` and `4`.  Determinant-level agreement does not force module agreement. -/
theorem not_nonempty_linearEquiv_cotangentModel_traceDefect_two [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    ¬ Nonempty (cotangentModel a 2 ≃ₗ[R] (Fin 2 → R ⧸ Ideal.span ({a ^ 2} : Set R))) := by
  rintro ⟨e⟩
  have h := e.length_eq
  rw [length_cotangentModel_two ha hmax, length_traceDefectModel_two ha hmax] at h
  exact absurd h (by decide)

end ThreeSheet

end Horizon

end HTGeometry.ConstraintRelativity
