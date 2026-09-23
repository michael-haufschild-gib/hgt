import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CongruenceOrderKaehlerDifferent

/-!
# The first infinitesimal thickening of the diagonal congruence order

Both the cotangent module and the trace-law defect of the diagonal congruence order are
annihilated by the square of the maximal ideal, so both are modules over the first square-zero
thickening `A/𝔪²`.  The residue ring of the order is the residue ring of the base.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace HTGeometry.ConstraintRelativity

open MvPolynomial

section Residue

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

/-- Evaluation of the presented congruence order at the origin. -/
noncomputable def congruenceEvalZero (a : R) (m : ℕ) :
    (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) →ₐ[R] R :=
  Ideal.Quotient.liftₐ (congruenceIdeal a m) (MvPolynomial.aeval fun _ => (0 : R)) (by
    intro x hx
    rw [congruenceIdeal] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨i, rfl⟩ | ⟨i, j, _, rfl⟩ <;> simp
    | zero => rw [map_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero])

theorem congruenceEvalZero_mk (p : MvPolynomial (Fin m) R) :
    congruenceEvalZero a m (Ideal.Quotient.mk _ p) = MvPolynomial.aeval (fun _ => (0 : R)) p :=
  rfl

theorem congruenceEvalZero_congruenceX (i : Fin m) :
    congruenceEvalZero a m (congruenceX a m i) = 0 := by
  rw [congruenceX, congruenceEvalZero_mk, MvPolynomial.aeval_X]

/-- The residue map of the congruence order. -/
noncomputable def residueMapA (a : R) (m : ℕ) :
    (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) →ₐ[R] (R ⧸ Ideal.span ({a} : Set R)) :=
  (Ideal.Quotient.mkₐ R (Ideal.span ({a} : Set R))).comp (congruenceEvalZero a m)

theorem residueMapA_surjective : Function.Surjective (residueMapA a m) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span ({a} : Set R)) y
  exact ⟨algebraMap R _ r, by
    show Ideal.Quotient.mk _ (congruenceEvalZero a m (algebraMap R _ r)) = _
    rw [AlgHom.commutes]
    rfl⟩

theorem exists_coord (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :
    ∃ (c₀ : R) (cc : Fin m → R),
      c = algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) c₀
        + ∑ k, algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (cc k)
            * congruenceX a m k := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨c₀, cc, hc⟩ := exists_linForm (a := a) p
  refine ⟨c₀, cc, ?_⟩
  have hsum : (∑ k, Ideal.Quotient.mk (congruenceIdeal a m) (C (cc k) * X k))
      = ∑ k, algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (cc k)
          * congruenceX a m k :=
    Finset.sum_congr rfl fun k _ => map_mul _ _ _
  have h1 : Ideal.Quotient.mk (congruenceIdeal a m) p
      = Ideal.Quotient.mk (congruenceIdeal a m) (linForm c₀ cc) := Ideal.Quotient.eq.2 hc
  rw [h1, linForm, map_add, map_sum, hsum]
  rfl

theorem ker_residueMapA :
    RingHom.ker (residueMapA a m) = maximalIdealA a m := by
  ext c
  rw [RingHom.mem_ker]
  constructor
  · intro hc
    obtain ⟨c₀, cc, rfl⟩ := exists_coord c
    have hc₀ : Ideal.Quotient.mk (Ideal.span ({a} : Set R)) c₀ = 0 := by
      rw [← hc]
      show _ = Ideal.Quotient.mk _ (congruenceEvalZero a m _)
      rw [map_add, map_sum, AlgHom.commutes]
      have hz : ∀ k : Fin m, congruenceEvalZero a m
          (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (cc k)
            * congruenceX a m k) = 0 := by
        intro k
        rw [map_mul, congruenceEvalZero_congruenceX, mul_zero]
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hz k, Finset.sum_const,
        smul_zero, add_zero]
      rfl
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1
      (Ideal.Quotient.eq_zero_iff_mem.1 hc₀)
    refine add_mem ?_ (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _
      (congruenceX_mem_maximalIdealA k))
    rw [hd, map_mul]
    exact Ideal.mul_mem_right _ _ (algebraMap_mem_maximalIdealA a m)
  · intro hc
    rw [maximalIdealA] at hc
    induction hc using Submodule.span_induction with
    | mem y hy =>
      rcases hy with hy | ⟨i, rfl⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        show Ideal.Quotient.mk _ (congruenceEvalZero a m (algebraMap R _ a)) = 0
        rw [AlgHom.commutes, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton.2 dvd_rfl
      · show Ideal.Quotient.mk _ (congruenceEvalZero a m (congruenceX a m i)) = 0
        rw [congruenceEvalZero_congruenceX, map_zero]
    | zero => rw [map_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The residue ring of the congruence order is the residue ring of the base. -/
noncomputable def residueEquiv :
    ((MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ maximalIdealA a m)
      ≃ₐ[R] (R ⧸ Ideal.span ({a} : Set R)) :=
  (Ideal.quotientEquivAlgOfEq R (ker_residueMapA (a := a) (m := m)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (residueMapA_surjective (a := a) (m := m)))

end Residue

/-! ## The square-zero thickening -/

section SquareZero

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [IsDomain R] [Invertible (2 : R)]

omit [IsDomain R] [Invertible (2 : R)] in
theorem sq_smul_cotangentModel (x : cotangentModel a m) : (a ^ (2 : ℕ)) • x = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun p => ?_)
  · show (a ^ (2 : ℕ)) • (x.1 i) = 0
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective
      (Ideal.span ({a ^ (2 : ℕ)} : Set R)) (x.1 i)
    rw [← hr, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton.2 ⟨r, rfl⟩
  · show (a ^ (2 : ℕ)) • (x.2 p) = 0
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (Ideal.span ({a} : Set R)) (x.2 p)
    rw [← hr, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton.2 ⟨a * r, by ring⟩

/-- The cotangent module of the congruence order is annihilated by `a²`. -/
theorem sq_smul_kaehler (ha : a ≠ 0)
    (ω : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]) : (a ^ (2 : ℕ)) • ω = 0 := by
  refine (kaehlerCongruenceEquiv (a := a) (m := m) ha).injective ?_
  rw [map_smul, map_zero]
  exact sq_smul_cotangentModel _

omit [IsDomain R] [Invertible (2 : R)] in
/-- The class `xⱼ dxᵢ` is annihilated by `a`. -/
theorem smul_a_congruenceX_smul_D (i j : Fin m) :
    (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a)
      • (congruenceX a m j • KaehlerDifferential.D R
        (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (congruenceX a m i)) = 0 := by
  classical
  have hsm : (congruenceX a m j
      • (Pi.single i 1 : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m))
      = Pi.single i (congruenceX a m j) := by
    funext l
    by_cases h : l = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  refine (kaehlerModelEquiv (a := a) (m := m)).injective ?_
  rw [map_zero, map_smul, map_smul,
    show (kaehlerModelEquiv (a := a) (m := m))
        (KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
          (congruenceX a m i))
      = Submodule.Quotient.mk
          (Pi.single i (1 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
            : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) from kaehlerToModel_D i,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hsm,
    Submodule.Quotient.mk_eq_zero, IsScalarTower.algebraMap_smul
      (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a]
  exact aSingle_mem_kaehlerRelations i j

theorem maximalIdealSq_smul_D (ha : a ≠ 0) {w : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m}
    (hw : w ∈ maximalIdealA a m * maximalIdealA a m) (i : Fin m) :
    w • KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      (congruenceX a m i) = 0 := by
  classical
  rw [maximalIdealA, Ideal.span_mul_span] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.1 hy
    have hax : ∀ j : Fin m,
        (algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a * congruenceX a m j)
          • KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
            (congruenceX a m i) = 0 := by
      intro j
      rw [mul_smul]
      exact smul_a_congruenceX_smul_D i j
    rcases hs with hs | ⟨j, rfl⟩
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      rcases ht with ht | ⟨l, rfl⟩
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        rw [← map_mul, IsScalarTower.algebraMap_smul, ← pow_two]
        exact sq_smul_kaehler ha _
      · exact hax l
    · rcases ht with ht | ⟨l, rfl⟩
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        rw [mul_comm]
        exact hax j
      · by_cases hjl : j = l
        · subst hjl
          rw [congruenceX_sq]
          exact hax j
        · rw [congruenceX_mul_of_ne hjl]
          exact zero_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
            (KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
              (congruenceX a m i))
  | zero =>
    exact zero_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      (KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        (congruenceX a m i))
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]

theorem maximalIdealSq_smul_eq_zero (ha : a ≠ 0)
    {w : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m}
    (hw : w ∈ maximalIdealA a m * maximalIdealA a m)
    (ω : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]) : w • ω = 0 := by
  have hmem : ω ∈ Submodule.span (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      (Set.range fun i : Fin m =>
        KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
          (congruenceX a m i)) := (span_D_congruenceX a m).symm ▸ Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact maximalIdealSq_smul_D ha hw i
  | zero => rw [smul_zero]
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_comm, hx, smul_zero]

/-- **Card `(26j1)`.**  The cotangent module of the congruence order is annihilated by `𝔪²`. -/
theorem maximalIdealSq_smul_kaehler (ha : a ≠ 0) :
    (maximalIdealA a m) • ((maximalIdealA a m) •
        (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
          Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.2 fun u hu x hx => ?_) bot_le
  rw [Submodule.mem_bot]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro v hv ω _
    rw [smul_smul]
    exact maximalIdealSq_smul_eq_zero ha (Ideal.mul_mem_mul hu hv) ω
  · intro y z hy hz
    rw [smul_add, hy, hz, add_zero]

variable [Invertible ((m : R) + 1)] [Invertible ((m : R) - 1)]

omit [IsDomain R] [Invertible (2 : R)] [Invertible ((m : R) - 1)] in
/-- **Card `(26j1)`.**  The trace-law defect is annihilated by `𝔪²`. -/
theorem maximalIdealSq_smul_traceDefect :
    (maximalIdealA a m) • ((maximalIdealA a m) •
      (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))) = ⊥ := by
  rw [maximalIdealA_smul_eq]
  exact maximalIdealA_smul_aMulA

omit [IsDomain R] [Invertible (2 : R)] [Invertible ((m : R) + 1)] [Invertible ((m : R) - 1)] in
theorem maximalIdeal_le_comap
    (φ : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m) :
    (maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])
      ≤ Submodule.comap φ ((maximalIdealA a m) •
        (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))) := by
  refine Submodule.smul_le.2 fun u hu ω _ => ?_
  rw [Submodule.mem_comap, map_smul]
  exact Submodule.smul_mem_smul hu Submodule.mem_top

/-- **Card `(26j2)`.**  The reduction of a source-linear comparison to the closed fibres. -/
noncomputable def headReduction
    (φ : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m) :
    (Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] ⧸
        ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
          Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])))
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m]
      (traceDefect a m ⧸ ((maximalIdealA a m) •
        (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m)))) :=
  Submodule.mapQ _ _ φ (maximalIdeal_le_comap φ)

omit [Invertible (2 : R)] in
/-- **Card `(26j2)`.**  Every source-linear comparison reduces to zero on the closed fibres. -/
theorem headReduction_eq_zero (ha : a ≠ 0)
    (φ : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m) :
    headReduction φ = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (φ ω) = 0
  rw [Submodule.Quotient.mk_eq_zero, maximalIdealA_smul_eq]
  exact soldering_range_le ha φ ω

omit [Invertible ((m : R) - 1)] in
/-- The closed fibre of the trace-law defect is the observer space. -/
noncomputable def traceDefectHeadEquiv :
    (traceDefect a m ⧸ aMul a (traceDefect a m))
      ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a} : Set R)) := by
  classical
  exact (Submodule.Quotient.equiv _ _ (traceDefectModelEquiv a m)
      (map_aMul (traceDefectModelEquiv a m))).trans
    ((piFibreEquiv a _).trans (LinearEquiv.piCongrRight fun _ => sqFibreEquiv a))

end SquareZero

/-! ## The closed cotangent fibre -/

section HeadFibre

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

/-- Postcomposition of a linear equivalence on a function space. -/
def piMapEquiv (S : Type*) [CommRing S] {ι M N : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (e : M ≃ₗ[S] N) : (ι → M) ≃ₗ[S] (ι → N) where
  toFun f i := e (f i)
  map_add' f g := funext fun i => map_add e (f i) (g i)
  map_smul' c f := funext fun i => map_smul e c (f i)
  invFun g i := e.symm (g i)
  left_inv f := funext fun i => e.symm_apply_apply (f i)
  right_inv g := funext fun i => e.apply_symm_apply (g i)

theorem map_smulTop_of_surjective {M N : Type*} [AddCommGroup M]
    [Module (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) M] [AddCommGroup N]
    [Module (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) N]
    (f : M →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] N) (hf : Function.Surjective f)
    (I : Ideal (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) :
    Submodule.map f (I • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) M))
      = I • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) N) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.smul_le.2 fun r hr x _ => ?_
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · refine Submodule.smul_le.2 fun r hr y _ => ?_
    obtain ⟨x, rfl⟩ := hf y
    rw [← map_smul]
    exact Submodule.mem_map_of_mem (Submodule.smul_mem_smul hr Submodule.mem_top)

theorem smulTop_pi :
    (maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m))
      = Submodule.pi Set.univ fun _ : Fin m =>
        (maximalIdealA a m : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
          (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) := by
  classical
  refine le_antisymm (Submodule.smul_le.2 fun u hu v _ => ?_) fun v hv => ?_
  · refine Submodule.mem_pi.2 fun i _ => ?_
    show u * v i ∈ maximalIdealA a m
    exact Ideal.mul_mem_right _ _ hu
  · rw [Submodule.mem_pi] at hv
    have hdec : v = ∑ i, (v i) • (Pi.single i 1
        : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) := by
      have hsingle : ∀ i : Fin m, (v i) • (Pi.single i 1
          : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) = Pi.single i (v i) := by
        intro i
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hsingle i, Finset.univ_sum_single]
    rw [hdec]
    exact sum_mem fun i _ =>
      Submodule.smul_mem_smul (hv i (Set.mem_univ i)) Submodule.mem_top

theorem kaehlerRelations_le_smulTop :
    kaehlerRelations a m
      ≤ (maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)) := by
  classical
  rw [smulTop_pi, kaehlerRelations, Submodule.span_le]
  rintro v (⟨i, rfl⟩ | ⟨i, j, _, rfl⟩) <;> refine Submodule.mem_pi.2 fun l _ => ?_
  · by_cases h : l = i
    · rw [h, Pi.single_eq_same]
      exact sub_mem (add_mem (congruenceX_mem_maximalIdealA i) (congruenceX_mem_maximalIdealA i))
        (algebraMap_mem_maximalIdealA a m)
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  · show (Pi.single i (congruenceX a m j) + Pi.single j (congruenceX a m i)
      : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) l ∈ _
    refine add_mem ?_ ?_
    · by_cases h : l = i
      · rw [h, Pi.single_eq_same]; exact congruenceX_mem_maximalIdealA j
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    · by_cases h : l = j
      · rw [h, Pi.single_eq_same]; exact congruenceX_mem_maximalIdealA i
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _

/-- The closed cotangent fibre is the observer space over the residue ring of the order. -/
noncomputable def kaehlerHeadEquiv :
    (Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])))
      ≃ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] (Fin m → (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ maximalIdealA a m) :=
  (Submodule.Quotient.equiv
      ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]))
      ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)))
      (kaehlerModelEquiv (a := a) (m := m))
      (map_smulTop_of_surjective (kaehlerModelEquiv (a := a) (m := m)).toLinearMap
        (kaehlerModelEquiv (a := a) (m := m)).surjective (maximalIdealA a m))).trans
    ((Submodule.quotEquivOfEq
        ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ((Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)))
        (Submodule.map (kaehlerRelations a m).mkQ
          ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m))))
        (map_smulTop_of_surjective (kaehlerRelations a m).mkQ
          (Submodule.mkQ_surjective _) (maximalIdealA a m)).symm).trans
      ((Submodule.quotientQuotientEquivQuotient (kaehlerRelations a m)
            ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)))
            kaehlerRelations_le_smulTop).trans
        ((Submodule.quotEquivOfEq _ _ smulTop_pi).trans (Submodule.quotientPi _))))

theorem smul_headFibre_eq_zero {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) M]
    {u : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m} (hu : u ∈ maximalIdealA a m)
    (x : M ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) M))) : u • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hu Submodule.mem_top

/-- Maps out of the residue ring are evaluation at one, on a module killed by the maximal
ideal. -/
noncomputable def evalOneEquiv {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) M]
    (h0 : ∀ u ∈ maximalIdealA a m, ∀ x : M, u • x = 0) :
    (((MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ maximalIdealA a m) →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] M) ≃ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] M where
  toFun φ := φ 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := Submodule.liftQ (maximalIdealA a m) (LinearMap.toSpanSingleton (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) M y)
    (fun u hu => h0 u hu y)
  left_inv φ := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show c • φ 1 = φ (Submodule.Quotient.mk c)
    rw [← map_smul]
    congr 1
    show c • (Submodule.Quotient.mk 1
      : (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ maximalIdealA a m)
      = Submodule.Quotient.mk c
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  right_inv y := by
    show (1 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) • y = y
    rw [one_smul]

/-- The reduction of source-linear comparisons to the closed fibres, as a linear map. -/
noncomputable def headReductionMap :
    (Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m) →ₗ[R]
      ((Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])))
        →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] (traceDefect a m ⧸ ((maximalIdealA a m) •
          (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))))) where
  toFun := headReduction
  map_add' φ ψ := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  map_smul' c φ := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- **Card `(26j3)`.**  The first soldering-obstruction space. -/
abbrev solderingObstructionSpace (a : R) (m : ℕ) : Type _ :=
  ((Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])))
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] (traceDefect a m ⧸ ((maximalIdealA a m) •
        (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m)))))
    ⧸ LinearMap.range (headReductionMap (a := a) (m := m))

variable [IsDomain R] [Invertible (2 : R)] [Invertible ((m : R) + 1)] [Invertible ((m : R) - 1)]

omit [IsDomain R] [Invertible (2 : R)] [Invertible ((m : R) - 1)] in
theorem restrictScalars_smulTop_traceDefect :
    (((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))).restrictScalars R)
      = aMul a (traceDefect a m) := by
  rw [maximalIdealA_smul_eq]
  rfl

omit [Invertible (2 : R)] [Invertible ((m : R) - 1)] in
/-- The closed fibre of the trace-law defect, in the form used by the obstruction space. -/
noncomputable def traceDefectHeadEquiv' :
    (traceDefect a m ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m)))) ≃ₗ[R] (Fin m → (R ⧸ Ideal.span ({a} : Set R))) :=
  (Submodule.quotEquivOfEq
      (((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))).restrictScalars R)
      (aMul a (traceDefect a m)) restrictScalars_smulTop_traceDefect).trans
    traceDefectHeadEquiv

omit [Invertible (2 : R)] [Invertible ((m : R) - 1)] in
/-- Source-linear maps between the closed fibres are the matrices on the observer directions. -/
noncomputable def homHeadEquiv :
    ((Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]))) →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] (traceDefect a m ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))))) ≃ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] (Fin m → (traceDefect a m ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))))) :=
  (LinearEquiv.arrowCongr (kaehlerHeadEquiv (a := a) (m := m)) (LinearEquiv.refl _ _)).trans
    ((LinearMap.lsum (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (fun _ : Fin m => (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ maximalIdealA a m)
        (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)).symm.trans
      (piMapEquiv (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (ι := Fin m)
        (evalOneEquiv (M := (traceDefect a m ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))))) fun _ hu x => smul_headFibre_eq_zero hu x)))

omit [Invertible (2 : R)] in
theorem range_headReductionMap (ha : a ≠ 0) :
    LinearMap.range (headReductionMap (a := a) (m := m)) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  exact LinearMap.ext fun φ => headReduction_eq_zero ha φ

/-- **Card `(26j3)`.**  The first soldering-obstruction space of the diagonal congruence order is
the matrix algebra on the observer directions over the residue ring. -/
noncomputable def solderingObstructionEquiv (ha : a ≠ 0) :
    solderingObstructionSpace a m ≃ₗ[R] Matrix (Fin m) (Fin m) (R ⧸ Ideal.span ({a} : Set R)) :=
  (Submodule.quotEquivOfEqBot _ (range_headReductionMap ha)).trans
    ((LinearEquiv.restrictScalars R (homHeadEquiv (a := a) (m := m))).trans
      (piMapEquiv R (ι := Fin m) (traceDefectHeadEquiv' (a := a) (m := m))))

omit [Invertible (2 : R)] in
/-- **Concrete sharp model.**  Only the zero head map lifts to a source-linear comparison, so
every nonzero tangent soldering has a nonzero first-order obstruction. -/
theorem headMap_eq_zero_of_lifts (ha : a ≠ 0)
    {f : (Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]))) →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] (traceDefect a m ⧸ ((maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m))))}
    (hf : ∃ φ : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m, headReduction φ = f) : f = 0 := by
  obtain ⟨φ, rfl⟩ := hf
  exact headReduction_eq_zero ha φ

end HeadFibre

end HTGeometry.ConstraintRelativity
