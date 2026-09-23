import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CongruenceOrderHorizon

/-!
# The congruence order acting on its own lattices

The sheet algebra `R^N` is an algebra over the presented congruence order
`A = R[x₁,…,x_m]/(xᵢ² − a xᵢ, xᵢxⱼ)`, and both the rescaled dual lattice and the rescaled order
are `A`-submodules of it.  This gives the trace-law defect its `A`-module structure.
-/

namespace HTGeometry.ConstraintRelativity

open MvPolynomial

section SheetAlgebra

variable {R : Type*} [CommRing R] (a : R) (m : ℕ)

/-- The presentation of the congruence order, as an algebra map to the sheet algebra. -/
noncomputable def congruenceEvalQuot :
    (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) →ₐ[R] (Fin (m + 1) → R) :=
  Ideal.Quotient.liftₐ (congruenceIdeal a m) (congruenceEval a m)
    fun _ hx => congruenceIdeal_le_ker hx

/-- The sheet algebra is an algebra over the presented congruence order. -/
noncomputable instance congruencePiAlgebra :
    Algebra (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) :=
  (congruenceEvalQuot a m).toRingHom.toAlgebra

instance congruencePiTower :
    IsScalarTower R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (AlgHom.commutes (congruenceEvalQuot a m) r).symm

variable {a m}

theorem algebraMap_congruencePi_mk (p : MvPolynomial (Fin m) R) :
    algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)
        (Ideal.Quotient.mk _ p) = congruenceEval a m p := rfl

theorem algebraMap_congruenceX (i : Fin m) :
    algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)
        (congruenceX a m i) = congruenceGen a m i := by
  rw [congruenceX, algebraMap_congruencePi_mk, congruenceEval, aeval_X]

theorem algebraMap_mem_congruenceOrder (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :
    algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) c
      ∈ congruenceOrder a (m + 1) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [algebraMap_congruencePi_mk, ← range_congruenceEval (a := a) (m := m)]
  exact ⟨p, rfl⟩

theorem congruencePi_smul (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
    (z : Fin (m + 1) → R) :
    c • z = algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) c * z :=
  Algebra.smul_def c z

end SheetAlgebra

/-! ## The lattices as modules over the congruence order -/

section Lattices

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

theorem mul_mem_scaledDual {v : Fin (m + 1) → R} (hv : v ∈ congruenceOrder a (m + 1))
    {z : Fin (m + 1) → R} (hz : z ∈ scaledDual a (m + 1)) :
    v * z ∈ scaledDual a (m + 1) := by
  classical
  obtain ⟨t, ht⟩ := mem_scaledDual.1 hz
  choose c hc using fun i => hv i (Fin.last m)
  have hvi : ∀ i, v i = v (Fin.last m) + a * c i := fun i => by linear_combination hc i
  refine mem_scaledDual.2 ⟨v (Fin.last m) * t + ∑ i, c i * z i, ?_⟩
  have hterm : ∀ i, (v * z) i = v (Fin.last m) * z i + a * (c i * z i) := by
    intro i
    show v i * z i = _
    rw [hvi i]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ht]
  ring

theorem mul_mem_scaledOrder {v : Fin (m + 1) → R} (hv : v ∈ congruenceOrder a (m + 1))
    {z : Fin (m + 1) → R} (hz : z ∈ scaledOrder a (m + 1)) :
    v * z ∈ scaledOrder a (m + 1) := by
  obtain ⟨w, hw, rfl⟩ := mem_scaledOrder.1 hz
  refine mem_scaledOrder.2 ⟨v * w, mul_mem hv hw, ?_⟩
  funext i
  show a * (v i * w i) = v i * (a * w i)
  ring

/-- The rescaled dual lattice as a module over the presented congruence order. -/
noncomputable def scaledDualA (a : R) (m : ℕ) :
    Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) where
  carrier := scaledDual a (m + 1)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c z hz := by
    rw [congruencePi_smul]
    exact mul_mem_scaledDual (algebraMap_mem_congruenceOrder c) hz

/-- The rescaled order as a module over the presented congruence order. -/
noncomputable def scaledOrderA (a : R) (m : ℕ) :
    Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) where
  carrier := scaledOrder a (m + 1)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c z hz := by
    rw [congruencePi_smul]
    exact mul_mem_scaledOrder (algebraMap_mem_congruenceOrder c) hz

theorem scaledDualA_restrictScalars :
    (scaledDualA a m).restrictScalars R = scaledDual a (m + 1) := rfl

theorem scaledOrderA_restrictScalars :
    (scaledOrderA a m).restrictScalars R = scaledOrder a (m + 1) := rfl

theorem scaledOrderA_le_scaledDualA : scaledOrderA a m ≤ scaledDualA a m :=
  scaledOrder_le_scaledDual a (m + 1)

/-- Quotients of submodules of the sheet algebra over the congruence order.  Instance search
does not find `Submodule.hasQuotient` through the induced algebra structure. -/
noncomputable instance sheetSubmoduleHasQuotient
    (P : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)) :
    HasQuotient ↥P (Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ↥P) :=
  @Submodule.hasQuotient (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ↥P _ _ _

/-- The trace-law defect of the congruence order, as a module over that order. -/
abbrev traceDefect (a : R) (m : ℕ) : Type _ :=
  ↥(scaledDualA a m) ⧸ Submodule.comap (scaledDualA a m).subtype (scaledOrderA a m)

end Lattices

/-! ## The trace-law defect in coordinates -/

section Coordinates

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [Invertible ((m : R) + 1)]

/-- The trace-law defect in coordinates. -/
noncomputable def traceDefectModelEquiv (a : R) (m : ℕ) [Invertible ((m : R) + 1)] :
    traceDefect a m ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a ^ (2 : ℕ)} : Set R)) :=
  scaledTraceDefectEquiv

theorem traceDefectModelEquiv_mk (z : ↥(scaledDualA a m)) :
    traceDefectModelEquiv a m (Submodule.Quotient.mk z)
      = traceCoord a m (z : Fin (m + 1) → R) := rfl

omit [Invertible ((m : R) + 1)] in
theorem traceDefect_mk_surjective (x : traceDefect a m) :
    ∃ z : ↥(scaledDualA a m), Submodule.Quotient.mk z = x :=
  Submodule.Quotient.mk_surjective _ x

omit [Invertible ((m : R) + 1)] in
theorem congruenceX_smul_coe (i : Fin m) (z : ↥(scaledDualA a m)) :
    ((congruenceX a m i • z : ↥(scaledDualA a m)) : Fin (m + 1) → R)
      = congruenceGen a m i * (z : Fin (m + 1) → R) := by
  show algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)
      (congruenceX a m i) * _ = _
  rw [algebraMap_congruenceX]

theorem traceCoord_congruenceGen_mul (i : Fin m) (z : Fin (m + 1) → R) (j : Fin m) :
    traceCoord a m (congruenceGen a m i * z) j
      = Submodule.Quotient.mk
          (a * z i.castSucc * ((if j = i then (1 : R) else 0) - ⅟((m : R) + 1))) := by
  classical
  have hval : ∀ l : Fin (m + 1), (congruenceGen a m i * z) l
      = (if l = i.castSucc then a * z i.castSucc else 0) := by
    intro l
    by_cases h : l = i.castSucc
    · rw [if_pos h, h]
      show a * (Pi.single i.castSucc (1 : R) : Fin (m + 1) → R) i.castSucc * z i.castSucc
        = a * z i.castSucc
      rw [Pi.single_eq_same, mul_one]
    · rw [if_neg h]
      show a * (Pi.single i.castSucc (1 : R) : Fin (m + 1) → R) l * z l = 0
      rw [Pi.single_eq_of_ne h, mul_zero, zero_mul]
  have hsum : ∑ l, (congruenceGen a m i * z) l = a * z i.castSucc := by
    rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hval l,
      Finset.sum_ite_eq' Finset.univ i.castSucc (fun _ => a * z i.castSucc),
      if_pos (Finset.mem_univ _)]
  rw [traceCoord_apply, hsum, hval]
  congr 1
  by_cases h : j = i
  · subst h
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg h, if_neg (fun hc => h (Fin.castSucc_injective m hc))]
    ring

/-- **Card `(26b)`.**  The source generators act on the trace-law defect through the
coordinate `zᵢ`, with the mean subtracted. -/
theorem traceDefectModelEquiv_congruenceX_smul (i : Fin m) (z : ↥(scaledDualA a m)) (j : Fin m) :
    traceDefectModelEquiv a m (Submodule.Quotient.mk (congruenceX a m i • z)) j
      = Submodule.Quotient.mk
          (a * (z : Fin (m + 1) → R) i.castSucc
            * ((if j = i then (1 : R) else 0) - ⅟((m : R) + 1))) := by
  rw [traceDefectModelEquiv_mk, congruenceX_smul_coe, traceCoord_congruenceGen_mul]

theorem traceDefectModelEquiv_algebraMap_smul (r : R) (z : ↥(scaledDualA a m)) :
    traceDefectModelEquiv a m (Submodule.Quotient.mk
        ((algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r) • z))
      = r • traceDefectModelEquiv a m (Submodule.Quotient.mk z) := by
  rw [traceDefectModelEquiv_mk, traceDefectModelEquiv_mk]
  have hc : ((((algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) r) • z)
      : ↥(scaledDualA a m)) : Fin (m + 1) → R) = r • (z : Fin (m + 1) → R) := by
    show algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)
        (algebraMap R _ r) * _ = _
    rw [← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
  rw [hc, map_smul]

end Coordinates

/-! ## The tangent-head soldering obstruction -/

section Soldering

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

/-- The differentiated square relation, in the Kähler module of the presented order. -/
theorem congruenceX_relation_smul_D (i : Fin m) :
    (congruenceX a m i + congruenceX a m i
        - algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a)
      • KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        (congruenceX a m i) = 0 := by
  have hsq := congrArg
    (KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m))
    (congruenceX_sq (a := a) i)
  rw [Derivation.leibniz, Derivation.leibniz, Derivation.map_algebraMap, smul_zero,
    add_zero] at hsq
  rw [sub_smul, add_smul]
  exact sub_eq_zero.2 hsq

/-- The Kähler module of the presented order is generated by the differentials of the source
generators. -/
theorem span_D_congruenceX (a : R) (m : ℕ) :
    Submodule.span (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        (Set.range fun i : Fin m =>
          KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
            (congruenceX a m i)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun ω _ => ?_
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective (kaehlerRelations a m)
    (kaehlerModelEquiv (a := a) (m := m) ω)
  have hsum : (Submodule.Quotient.mk v
      : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)
      = ∑ i, (v i) • Submodule.Quotient.mk
          (Pi.single i (1 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
            : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) := by
    have hmap := map_sum ((kaehlerRelations a m).mkQ) (fun i => Pi.single i (v i)) Finset.univ
    rw [Finset.univ_sum_single] at hmap
    rw [show (Submodule.Quotient.mk v
        : (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ⧸ kaehlerRelations a m)
      = (kaehlerRelations a m).mkQ v from rfl, hmap]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Submodule.mkQ_apply, model_single]
  have hω : ω = ∑ i, (v i) •
      KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
        (congruenceX a m i) := by
    refine (kaehlerModelEquiv (a := a) (m := m)).injective ?_
    rw [map_sum, ← hv, hsum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul]
      congr 1
      exact (kaehlerToModel_D (R := R) (a := a) (m := m) i).symm
  rw [hω]
  exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_aMul_of_equiv {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (e : M ≃ₗ[R] N) {x : M} (h : e x ∈ aMul a N) : x ∈ aMul a M := by
  rw [mem_aMul] at h ⊢
  obtain ⟨u, hu⟩ := h
  refine ⟨e.symm u, ?_⟩
  rw [← map_smul, hu, e.symm_apply_apply]

variable [IsDomain R] [Invertible ((m : R) + 1)] [Invertible ((m : R) - 1)]

/-- If the differentiated square relation annihilates a class in the trace-law defect, that
class lies in `a·L`. -/
theorem mem_aMul_of_relation (ha : a ≠ 0) (i : Fin m) {ℓ : traceDefect a m}
    (hℓ : (congruenceX a m i + congruenceX a m i
        - algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a) • ℓ = 0) :
    ℓ ∈ aMul a (traceDefect a m) := by
  classical
  obtain ⟨z, rfl⟩ := traceDefect_mk_surjective ℓ
  set zz : Fin (m + 1) → R := (z : Fin (m + 1) → R) with hzz
  set n : R := ⅟((m : R) + 1) with hn
  have hnN : n * ((m : R) + 1) = 1 := invOf_mul_self _
  obtain ⟨t, ht⟩ := mem_scaledDual.1 z.2
  rw [← hzz] at ht
  have hval : ∀ j : Fin m,
      traceDefectModelEquiv a m (Submodule.Quotient.mk z) j
        = Submodule.Quotient.mk (zz j.castSucc - n * ∑ l, zz l) := fun j => by
    rw [traceDefectModelEquiv_mk, traceCoord_apply]
  have hsmul : ∀ j : Fin m,
      traceDefectModelEquiv a m (Submodule.Quotient.mk (congruenceX a m i • z)) j
        = Submodule.Quotient.mk
            (a * zz i.castSucc * ((if j = i then (1 : R) else 0) - n)) := fun j =>
    traceDefectModelEquiv_congruenceX_smul i z j
  have h0 : traceDefectModelEquiv a m (Submodule.Quotient.mk (congruenceX a m i • z))
      + traceDefectModelEquiv a m (Submodule.Quotient.mk (congruenceX a m i • z))
      - a • traceDefectModelEquiv a m (Submodule.Quotient.mk z) = 0 := by
    have h := congrArg (traceDefectModelEquiv a m) hℓ
    rw [map_zero] at h
    rw [← h, ← Submodule.Quotient.mk_smul, sub_smul, add_smul, Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_add, map_sub, map_add, traceDefectModelEquiv_algebraMap_smul]
  have hkey : ∀ j : Fin m, a ∣ 2 * (zz i.castSucc * ((if j = i then (1 : R) else 0) - n))
      - (zz j.castSucc - n * ∑ l, zz l) := by
    intro j
    have hj := congrFun h0 j
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, hsmul, hval,
      ← Submodule.Quotient.mk_smul, smul_eq_mul, ← Submodule.Quotient.mk_add,
      ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton] at hj
    obtain ⟨c, hc⟩ := hj
    refine ⟨c, ?_⟩
    have hcan : a * (2 * (zz i.castSucc * ((if j = i then (1 : R) else 0) - n))
        - (zz j.castSucc - n * ∑ l, zz l)) = a * (a * c) := by
      linear_combination hc
    exact mul_left_cancel₀ ha hcan
  have hdiag : a ∣ zz i.castSucc := by
    have h := hkey i
    rw [if_pos rfl] at h
    have h1 : a ∣ zz i.castSucc * (((m : R) - 1) * n) := by
      obtain ⟨c, hc⟩ := h
      refine ⟨c - n * t, ?_⟩
      linear_combination hc + zz i.castSucc * hnN - n * ht
    obtain ⟨c, hc⟩ := h1
    refine ⟨c * (⅟((m : R) - 1) * ((m : R) + 1)), ?_⟩
    have hm1 : ((m : R) - 1) * ⅟((m : R) - 1) = 1 := mul_invOf_self _
    calc zz i.castSucc
        = zz i.castSucc * (((m : R) - 1) * n) * (⅟((m : R) - 1) * ((m : R) + 1)) := by
          linear_combination (-(zz i.castSucc) * (n * ((m : R) + 1))) * hm1
            - zz i.castSucc * hnN
      _ = a * (c * (⅟((m : R) - 1) * ((m : R) + 1))) := by rw [hc]; ring
  have hall : ∀ j : Fin m, a ∣ zz j.castSucc := by
    intro j
    by_cases hji : j = i
    · rw [hji]; exact hdiag
    · have h := hkey j
      rw [if_neg hji] at h
      obtain ⟨c, hc⟩ := h
      obtain ⟨e, he⟩ := hdiag
      exact ⟨n * t - 2 * n * e - c, by linear_combination -hc + n * ht - 2 * n * he⟩
  choose u hu using hall
  refine mem_aMul_of_equiv (traceDefectModelEquiv a m) ?_
  rw [mem_aMul]
  refine ⟨fun j => Submodule.Quotient.mk (u j - n * t), ?_⟩
  funext j
  rw [Pi.smul_apply, hval, ← Submodule.Quotient.mk_smul, smul_eq_mul]
  congr 1
  linear_combination n * ht - hu j

omit [IsDomain R] [Invertible ((m : R) + 1)] [Invertible ((m : R) - 1)] in
theorem aMul_smul_mem (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
    {x : traceDefect a m} (hx : x ∈ aMul a (traceDefect a m)) :
    c • x ∈ aMul a (traceDefect a m) := by
  rw [mem_aMul] at hx ⊢
  obtain ⟨w, rfl⟩ := hx
  exact ⟨c • w, smul_comm a c w⟩

/-- **Card `(26e)`.**  Every source-linear comparison from the cotangent module to the trace-law
defect has image inside `a·L`. -/
theorem soldering_range_le (ha : a ≠ 0)
    (φ : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m)
    (ω : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]) :
    φ ω ∈ aMul a (traceDefect a m) := by
  have hmem : ω ∈ Submodule.span (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      (Set.range fun i : Fin m =>
        KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
          (congruenceX a m i)) := (span_D_congruenceX a m).symm ▸ Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine mem_aMul_of_relation ha i ?_
    rw [← map_smul, congruenceX_relation_smul_D, map_zero]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact aMul_smul_mem c hx

/-- The `a`-multiples in the trace-law defect, as a submodule over the congruence order. -/
noncomputable def aMulA (a : R) (m : ℕ) :
    Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (traceDefect a m) where
  carrier := aMul a (traceDefect a m)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c _ hx := aMul_smul_mem c hx

/-- **Card `(26g)`.**  The tangent-head reduction of every source-linear comparison from the
cotangent module to the trace-law defect is identically zero. -/
theorem soldering_head_eq_zero (ha : a ≠ 0)
    (φ : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m) :
    (aMulA a m).mkQ.comp φ = 0 := by
  refine LinearMap.ext fun ω => ?_
  exact (Submodule.Quotient.mk_eq_zero _).2 (soldering_range_le ha φ ω)

/-- The maximal ideal of the congruence order. -/
noncomputable def maximalIdealA (a : R) (m : ℕ) :
    Ideal (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :=
  Ideal.span ({algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a}
    ∪ Set.range (congruenceX a m))

omit [IsDomain R] [Invertible ((m : R) - 1)] in
theorem congruenceX_smul_mem_aMul (i : Fin m) (ℓ : traceDefect a m) :
    congruenceX a m i • ℓ ∈ aMul a (traceDefect a m) := by
  classical
  obtain ⟨z, rfl⟩ := traceDefect_mk_surjective ℓ
  refine mem_aMul_of_equiv (traceDefectModelEquiv a m) ?_
  rw [mem_aMul]
  refine ⟨fun j => Submodule.Quotient.mk
    ((z : Fin (m + 1) → R) i.castSucc
      * ((if j = i then (1 : R) else 0) - ⅟((m : R) + 1))), ?_⟩
  funext j
  rw [Pi.smul_apply, show (congruenceX a m i • (Submodule.Quotient.mk z : traceDefect a m))
      = Submodule.Quotient.mk (congruenceX a m i • z) from
    (Submodule.Quotient.mk_smul _ _ _).symm,
    traceDefectModelEquiv_congruenceX_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul]
  congr 1
  ring

omit [IsDomain R] [Invertible ((m : R) - 1)] in
/-- **Card `(26b)`, ideal form.**  The maximal ideal acts on the trace-law defect exactly as `a`
does. -/
theorem maximalIdealA_smul_eq :
    (maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      (traceDefect a m)) = aMulA a m := by
  refine le_antisymm (Submodule.smul_le.2 fun c hc ℓ _ => ?_) ?_
  · rw [maximalIdealA] at hc
    induction hc using Submodule.span_induction with
    | mem y hy =>
      rcases hy with hy | ⟨i, rfl⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        show _ ∈ aMul a (traceDefect a m)
        rw [mem_aMul]
        exact ⟨ℓ, (IsScalarTower.algebraMap_smul
          (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a ℓ).symm⟩
      · exact congruenceX_smul_mem_aMul i ℓ
    | zero =>
      have hz : (0 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) • ℓ = 0 :=
        zero_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ℓ
      rw [hz]
      exact zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul r x _ hx => rw [smul_eq_mul, mul_smul]; exact aMul_smul_mem r hx
  · rintro ℓ hℓ
    obtain ⟨w, rfl⟩ := mem_aMul.1 hℓ
    rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a]
    exact Submodule.smul_mem_smul
      (Ideal.subset_span (Or.inl rfl)) Submodule.mem_top

end Soldering

end HTGeometry.ConstraintRelativity
