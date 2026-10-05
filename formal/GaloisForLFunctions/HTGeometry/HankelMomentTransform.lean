import GaloisForLFunctions.HTGeometry.HankelLeadingChart

/-!
# Translation and reversal of moment coordinates

Read the coordinate `x_n` as the moment `∫ T^n`.  Translating the measure by `t` and reversing the
moment window give two automorphisms of `K[x_0, …, x_{N−1}]`:

* `momentShift t : x_n ↦ Σ_k binom(n, k) t^{n−k} x_k`, the moment of `(T + t)^n`;
* `momentRev : x_n ↦ x_{N−1−n}`.

Both preserve every Hankel secant ideal.  The shift intertwines the atomic parameterization with the
translation `T_j ↦ T_j + t` of the nodes, so it maps the kernel into itself; the reversal sends each
maximal minor to another one, its matrix being the reversal of rows and columns of the minor with
the reflected column set.  Composing them moves the leading-block chart to the charts
`δ_t = (shift_t ∘ rev)(δ)`, each again integrally closed.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

section Ring

variable (K : Type*) [CommRing K] (N : ℕ)

/-- `f ↦ Σ_{k<N} f_k x_k`: the moment of a polynomial of degree `< N`. -/
def momentEval : Polynomial K →ₗ[K] MvPolynomial (Fin N) K :=
  ∑ k : Fin N, (Polynomial.lcoeff K k).smulRight (X k)

theorem momentEval_apply (f : Polynomial K) :
    momentEval K N f = ∑ k : Fin N, f.coeff k • (X k : MvPolynomial (Fin N) K) := by
  simp [momentEval, LinearMap.sum_apply, LinearMap.smulRight_apply]

theorem momentEval_X_pow (n : Fin N) :
    momentEval K N (Polynomial.X ^ (n : ℕ)) = X n := by
  classical
  rw [momentEval_apply, Finset.sum_eq_single n]
  · rw [Polynomial.coeff_X_pow_self, one_smul]
  · intro k _ hk
    rw [Polynomial.coeff_X_pow, if_neg (fun h => hk (Fin.ext h)), zero_smul]
  · intro h; exact absurd (Finset.mem_univ n) h

/-- The moment shift `x_n ↦ moment of (T + t)^n`. -/
def momentShift (t : K) : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K :=
  aeval fun n => momentEval K N ((Polynomial.X + Polynomial.C t) ^ (n : ℕ))

theorem momentShift_X (t : K) (n : Fin N) :
    momentShift K N t (X n) = momentEval K N ((Polynomial.X + Polynomial.C t) ^ (n : ℕ)) :=
  aeval_X _ _

theorem natDegree_X_add_C_pow_le (t : K) (n : ℕ) :
    ((Polynomial.X + Polynomial.C t) ^ n).natDegree ≤ n := by
  refine (Polynomial.natDegree_pow_le_of_le (m := 1) (p := Polynomial.X + Polynomial.C t) n ?_).trans
    (by rw [mul_one])
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  rw [Polynomial.natDegree_C, max_le_iff]
  exact ⟨Polynomial.natDegree_X_le (R := K), zero_le_one⟩

theorem momentShift_momentEval (t : K) {f : Polynomial K} (hf : f.natDegree < N) :
    momentShift K N t (momentEval K N f) =
      momentEval K N (f.comp (Polynomial.X + Polynomial.C t)) := by
  rw [momentEval_apply, map_sum, Polynomial.comp, Polynomial.eval₂_eq_sum_range' _ hf,
    map_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, momentShift_X, Polynomial.C_mul', map_smul]

theorem momentShift_comp (s t : K) :
    (momentShift K N t).comp (momentShift K N s) = momentShift K N (s + t) := by
  refine MvPolynomial.algHom_ext fun n => ?_
  rw [AlgHom.comp_apply, momentShift_X, momentShift_momentEval K N t
    (lt_of_le_of_lt (natDegree_X_add_C_pow_le K s n) n.isLt), momentShift_X]
  congr 1
  rw [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
    Polynomial.C_add]
  ring

theorem momentShift_zero : momentShift K N 0 = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun n => ?_
  rw [momentShift_X, map_zero, add_zero, momentEval_X_pow, AlgHom.id_apply]

/-- The moment shift as an automorphism. -/
def momentShiftEquiv (t : K) : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K :=
  AlgEquiv.ofAlgHom (momentShift K N t) (momentShift K N (-t))
    (by rw [momentShift_comp, neg_add_cancel, momentShift_zero])
    (by rw [momentShift_comp, add_neg_cancel, momentShift_zero])

theorem momentShiftEquiv_apply (t : K) (p : MvPolynomial (Fin N) K) :
    momentShiftEquiv K N t p = momentShift K N t p := rfl

/-- The moment reversal `x_n ↦ x_{N−1−n}`. -/
def momentRev : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K :=
  renameEquiv K Fin.revPerm

theorem momentRev_X (n : Fin N) : momentRev K N (X n) = X (Fin.rev n) := by
  simp [momentRev]

/-! ### The secant ideals are preserved -/

/-- Translation of the nodes of the atomic parameterization. -/
def nodeShift (r : ℕ) (t : K) :
    MvPolynomial (Fin r × Fin 2) K →ₐ[K] MvPolynomial (Fin r × Fin 2) K :=
  aeval fun a => if a.2 = 1 then X a + MvPolynomial.C t else X a

theorem secantParameterization_momentEval (r : ℕ) {f : Polynomial K} (hf : f.natDegree < N) :
    RHTower.finiteHankelSecantParameterization K N r (momentEval K N f) =
      ∑ j : Fin r, X (j, (0 : Fin 2)) *
        Polynomial.aeval (X (j, (1 : Fin 2)) : MvPolynomial (Fin r × Fin 2) K) f := by
  rw [momentEval_apply, map_sum]
  simp only [RHTower.finiteHankelSecantParameterization_X, RHTower.deningerHankelSecantMoment,
    Algebra.smul_def, map_mul, MvPolynomial.algebraMap_eq]
  have hC : ∀ c : K, RHTower.finiteHankelSecantParameterization K N r (MvPolynomial.C c) =
      MvPolynomial.C c := by
    intro c
    simp [RHTower.finiteHankelSecantParameterization, RHTower.deningerHankelSecantParameterization]
  simp only [hC, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.aeval_eq_sum_range' hf, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring

theorem secantParameterization_comp_momentShift (r : ℕ) (t : K) :
    (RHTower.finiteHankelSecantParameterization K N r).comp
        (momentShift K N t : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) K) =
      (nodeShift K r t : MvPolynomial (Fin r × Fin 2) K →+* _).comp
        (RHTower.finiteHankelSecantParameterization K N r) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) fun n => ?_
  · simp [RHTower.finiteHankelSecantParameterization, RHTower.deningerHankelSecantParameterization,
      nodeShift]
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, momentShift_X,
      secantParameterization_momentEval K N r
        (lt_of_le_of_lt (natDegree_X_add_C_pow_le K t n) n.isLt),
      RHTower.finiteHankelSecantParameterization_X, RHTower.deningerHankelSecantMoment,
      RingHom.coe_coe, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, nodeShift, aeval_X, map_add, Polynomial.aeval_X,
      Polynomial.aeval_C, MvPolynomial.algebraMap_eq]
    rw [if_neg (show (0 : Fin 2) ≠ 1 by decide), if_pos trivial]

theorem momentShift_mem_secantIdeal (r : ℕ) (t : K) {p : MvPolynomial (Fin N) K}
    (hp : p ∈ RHTower.finiteHankelSecantIdeal K N r) :
    momentShift K N t p ∈ RHTower.finiteHankelSecantIdeal K N r := by
  rw [RHTower.finiteHankelSecantIdeal_eq_parameterization_ker, RingHom.mem_ker] at hp ⊢
  have h := congrArg (fun φ : MvPolynomial (Fin N) K →+* _ => φ p)
    (secantParameterization_comp_momentShift K N r t)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at h
  rw [h, hp, map_zero]

theorem map_momentShiftEquiv_secantIdeal (r : ℕ) (t : K) :
    (RHTower.finiteHankelSecantIdeal K N r).map (momentShiftEquiv K N t) =
      RHTower.finiteHankelSecantIdeal K N r := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    exact momentShift_mem_secantIdeal K N r t hp
  · intro p hp
    have hq := momentShift_mem_secantIdeal K N r (-t) hp
    have hpq : p = momentShiftEquiv K N t (momentShift K N (-t) p) := by
      rw [momentShiftEquiv_apply, ← AlgHom.comp_apply, momentShift_comp, neg_add_cancel,
        momentShift_zero, AlgHom.id_apply]
    rw [hpq]
    exact Ideal.mem_map_of_mem _ hq

/-- The reflected column selection of a maximal minor. -/
def reflectCols {n : ℕ} (c : Fin n → ℕ) : Fin n → ℕ := fun j => N - n - c (Fin.rev j)

theorem reflectCols_bound {n : ℕ} {c : Fin n → ℕ} (hbound : ∀ j, n + c j ≤ N) (j : Fin n) :
    n + reflectCols N c j ≤ N := by
  unfold reflectCols; have := hbound (Fin.rev j); omega

theorem reflectCols_strictMono {n : ℕ} {c : Fin n → ℕ} (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) : StrictMono (reflectCols N c) := by
  intro a b hab
  have h1 := hc (Fin.rev_lt_rev.mpr hab)
  have h2 := hbound (Fin.rev a)
  unfold reflectCols
  omega

theorem momentRev_maximalMinor {n : ℕ} (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N) :
    momentRev K N (RHTower.finiteHankelMaximalMinorOver K c hbound) =
      RHTower.finiteHankelMaximalMinorOver K (reflectCols N c) (reflectCols_bound N hbound) := by
  classical
  rw [RHTower.finiteHankelMaximalMinorOver, RHTower.finiteHankelMaximalMinorOver]
  rw [show (momentRev K N : MvPolynomial (Fin N) K → MvPolynomial (Fin N) K) =
      ((momentRev K N : MvPolynomial (Fin N) K ≃ₐ[K] _) : MvPolynomial (Fin N) K →+* _) from rfl,
    RingHom.map_det]
  conv_rhs => rw [← Matrix.det_submatrix_equiv_self Fin.revPerm]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, RingHom.coe_coe,
    momentRev_X]
  refine congrArg (X (R := K)) (Fin.ext ?_)
  simp only [RHTower.finiteHankelIndex, Fin.val_rev, Fin.revPerm_apply, reflectCols, Fin.rev_rev]
  have := hbound j
  have := i.isLt
  omega

theorem momentRev_momentRev (p : MvPolynomial (Fin N) K) : momentRev K N (momentRev K N p) = p := by
  simp only [momentRev, renameEquiv_apply, MvPolynomial.rename_rename]
  convert MvPolynomial.rename_id_apply p
  funext n
  simp

theorem map_momentRev_secantIdeal (r : ℕ) :
    (RHTower.finiteHankelSecantIdeal K N r).map (momentRev K N) =
      RHTower.finiteHankelSecantIdeal K N r := by
  have hle : ∀ s : ℕ, (RHTower.finiteHankelSecantIdeal K N s).map (momentRev K N) ≤
      RHTower.finiteHankelSecantIdeal K N s := by
    intro s
    rw [RHTower.finiteHankelSecantIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨p, ⟨c, hbound, hc, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨reflectCols N c, reflectCols_bound N hbound,
      reflectCols_strictMono N hbound hc, ?_⟩
    exact momentRev_maximalMinor K N c hbound
  refine le_antisymm (hle r) ?_
  intro p hp
  rw [← momentRev_momentRev K N p]
  exact Ideal.mem_map_of_mem _ (hle r (Ideal.mem_map_of_mem _ hp))

theorem momentRev_mem_secantIdeal (r : ℕ) {p : MvPolynomial (Fin N) K}
    (hp : p ∈ RHTower.finiteHankelSecantIdeal K N r) :
    momentRev K N p ∈ RHTower.finiteHankelSecantIdeal K N r := by
  rw [← map_momentRev_secantIdeal K N r]
  exact Ideal.mem_map_of_mem _ hp

end Ring

/-! ### The moved charts -/

section Field

variable (K : Type) [Field K]

/-- The chart transform `rev` followed by the shift by `t`. -/
def momentChartEquiv (N : ℕ) (t : K) : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K :=
  (momentRev K N).trans (momentShiftEquiv K N t)

theorem momentChartEquiv_X (N : ℕ) (t : K) (n : Fin N) :
    momentChartEquiv K N t (X n) =
      momentEval K N ((Polynomial.X + Polynomial.C t) ^ (N - 1 - (n : ℕ))) := by
  rw [momentChartEquiv, AlgEquiv.trans_apply, momentRev_X, momentShiftEquiv_apply, momentShift_X,
    Fin.val_rev]
  congr 2
  omega

theorem map_momentChartEquiv_secantIdeal (N r : ℕ) (t : K) :
    (RHTower.finiteHankelSecantIdeal K N r).map (momentChartEquiv K N t) =
      RHTower.finiteHankelSecantIdeal K N r := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, momentChartEquiv]
    erw [AlgEquiv.trans_apply]
    rw [momentShiftEquiv_apply]
    exact momentShift_mem_secantIdeal K N r t (momentRev_mem_secantIdeal K N r hp)
  · intro p hp
    have hq : momentRev K N (momentShift K N (-t) p) ∈ RHTower.finiteHankelSecantIdeal K N r :=
      momentRev_mem_secantIdeal K N r (momentShift_mem_secantIdeal K N r (-t) hp)
    have hpq : p = momentChartEquiv K N t (momentRev K N (momentShift K N (-t) p)) := by
      rw [momentChartEquiv, AlgEquiv.trans_apply, momentRev_momentRev, momentShiftEquiv_apply,
        ← AlgHom.comp_apply, momentShift_comp, neg_add_cancel, momentShift_zero, AlgHom.id_apply]
    rw [hpq]
    exact Ideal.mem_map_of_mem _ hq

/-- The induced automorphism of the Hankel secant ring. -/
def hankelSecantChartEquiv (N r : ℕ) (t : K) : HankelSecantRing K N r ≃ₐ[K] HankelSecantRing K N r :=
  Ideal.quotientEquivAlg _ _ (momentChartEquiv K N t)
    (map_momentChartEquiv_secantIdeal K N r t).symm

/-- The moved chart `δ_t`. -/
def hankelChartElemAt (N r : ℕ) (t : K) : HankelSecantRing K N r :=
  hankelSecantChartEquiv K N r t (hankelChartElem K N r)

theorem hankelChartElemAt_eq (N r : ℕ) (t : K) :
    hankelChartElemAt K N r t =
      Ideal.Quotient.mk _ (momentChartEquiv K N t (hankelLeadMinor K N r)) := by
  rw [hankelChartElemAt, hankelChartElem_eq]
  rfl

/-- **Every moved chart is integrally closed.** -/
theorem isIntegrallyClosed_hankelChartAt [CharZero K] {N r : ℕ} (hN : 2 * r ≤ N) (t : K) :
    IsIntegrallyClosed (Localization.Away (hankelChartElemAt K N r t)) := by
  haveI := isIntegrallyClosed_hankelChart K hN
  have e : Localization.Away (hankelChartElem K N r) ≃+*
      Localization.Away (hankelChartElemAt K N r t) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (hankelChartElem K N r))
      (T := Submonoid.powers (hankelChartElemAt K N r t)) _ _
      (hankelSecantChartEquiv K N r t : HankelSecantRing K N r ≃+* HankelSecantRing K N r)
      (by rw [Submonoid.map_powers]; rfl)
  exact IsIntegrallyClosed.of_equiv e

end Field

end

end GaloisForLFunctions.HTGeometry
