import GaloisForLFunctions.HTGeometry.HankelIncidenceRing
import GaloisForLFunctions.RHTower.Deninger.DeningerHankelHigherRankGroebner
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The secant ideal is the kernel of the moments on the incidence variety

Let `B_j = T/(ℓ_0, …, ℓ_{j-1})` (`j + r ≤ N`): only the moments `v_0, …, v_{j+r-1}` occur in the
equations, the others are free.  The relevant ideal of `K[x_0, …, x_{N-1}]` is `secantIdealUpTo`,
the `(r+1)`-minors of the Hankel matrix with columns `< j`; for `j = N - r` it is the secant ideal
`I_r`, and in general it is `I_r` of the first `j + r` moments extended by the free ones.

Let `μ` be such a minor.  On `B_j` the row vector `z` of coefficients of `G` annihilates the Hankel
matrix (its products with the columns are Hankel equations), so `det(M) · z = 0` by the adjugate, and
`det(M) · G(t) = 0` for every node `t`: every such minor dies on every evaluation chart.

Conversely, over the coefficient ring `R = K[x_{j+r}, …, x_{N-1}]` of the free moments, the atom
parametrization `z ↦ coeff(∏_l (X - t_l))`, `v_n ↦ ∑_l c_l t_l^n` (`n < j + r`), `v_n ↦ x_n`
(`n ≥ j + r`) kills every Hankel equation (`G(t_l) = 0`) and sends `G(0)` to `∏_l (-t_l) ≠ 0`.  A
moment polynomial that dies on the chart `G(0) ≠ 0` is therefore killed by the atom
parametrization over `R`, and lies in the secant ideal over `R`
(`finiteHankelSecantIdeal_eq_parameterization_ker`, valid over every commutative ring).

* `HTGeometry.secantIdealUpTo`, `HTGeometry.secantIdealUpTo_self`.
* `HTGeometry.splitEquiv`, `HTGeometry.map_splitEquiv_secantIdealUpTo`.
* `HTGeometry.chartForm_mul_minor_mem` : minors die on every chart.
* `HTGeometry.mem_secantIdealUpTo_of_chartZero` : the converse.
-/

namespace HTGeometry

open Polynomial

universe u

variable {K : Type u} [Field K] {r N : ℕ}

variable (K r N) in
/-- Moment polynomials inside the incidence ring: `x_n ↦ v_n`. -/
noncomputable def momentEmbed : MvPolynomial (Fin N) K →ₐ[K] IncRing K r N :=
  MvPolynomial.rename Sum.inr

theorem momentEmbed_X (n : Fin N) : momentEmbed K r N (MvPolynomial.X n) = vv K r N n := by
  simp [momentEmbed, vv]

/-! ## The secant ideal of the first `j + r` moments -/

/-- **The secant ideal of the first `j + r` moments**: the `(r+1)`-minors of the Hankel matrix of
`x_0, …, x_{N-1}` whose columns are `< j`. -/
noncomputable def secantIdealUpTo (K : Type u) [Field K] (N r j : ℕ) : Ideal (MvPolynomial (Fin N) K) :=
  Ideal.span {p | ∃ (c : Fin (r + 1) → ℕ) (hbound : ∀ i, r + 1 + c i ≤ N), StrictMono c ∧
    (∀ i, c i < j) ∧ p = RHTower.finiteHankelMaximalMinorOver K c hbound}

/-- For `j = N - r` it is the Hankel secant ideal. -/
theorem secantIdealUpTo_self : secantIdealUpTo K N r (N - r) = RHTower.finiteHankelSecantIdeal K N r := by
  rw [secantIdealUpTo, RHTower.finiteHankelSecantIdeal, RHTower.finiteHankelMaximalMinorSetOver]
  congr 1
  ext p
  constructor
  · rintro ⟨c, hb, hc, -, rfl⟩
    exact ⟨c, hb, hc, rfl⟩
  · rintro ⟨c, hb, hc, rfl⟩
    exact ⟨c, hb, hc, fun i => by have := hb i; omega, rfl⟩

/-! ## Minors die on every chart -/

/-- **Every Hankel `(r+1)`-minor with columns `< j` dies on every evaluation chart of `B_j`.** -/
theorem chartForm_mul_minor_mem (t : K) {j : ℕ} {c : Fin (r + 1) → ℕ} (hbound : ∀ i, r + 1 + c i ≤ N)
    (hc : ∀ i, c i < j) :
    chartForm K r N t * momentEmbed K r N (RHTower.finiteHankelMaximalMinorOver K c hbound)
      ∈ hankelIdeal K r N j := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
  set π := Ideal.Quotient.mk (hankelIdeal K r N j)
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) (IncRing K r N ⧸ hankelIdeal K r N j) :=
    fun i i' => π (vv K r N (RHTower.finiteHankelIndex c hbound i i')) with hM
  have hdet : π (momentEmbed K r N (RHTower.finiteHankelMaximalMinorOver K c hbound)) = M.det := by
    rw [RHTower.finiteHankelMaximalMinorOver, AlgHom.map_det, RingHom.map_det]
    congr 1
    ext i i'
    simp [hM, momentEmbed_X]
  set z : Fin (r + 1) → IncRing K r N ⧸ hankelIdeal K r N j := fun i => π (zv K r N i)
  have hz : Matrix.vecMul z M = 0 := by
    funext i'
    have hb := hbound i'
    have hmem := hankelEq_mem_hankelIdeal (K := K) (r := r) (N := N) (hc i')
    rw [← Ideal.Quotient.eq_zero_iff_mem, hankelEq_eq, map_sum] at hmem
    rw [Matrix.vecMul, dotProduct, Pi.zero_apply, ← hmem]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, vAt, dif_pos (by omega)]
    rfl
  have hdz : M.det • z = 0 := by
    have h1 : Matrix.vecMul z (M * M.adjugate) = M.det • z := by
      rw [Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [← h1, ← Matrix.vecMul_vecMul, hz, Matrix.zero_vecMul]
  have hchart : π (chartForm K r N t)
      = ∑ i : Fin (r + 1), z i * π (algebraMap K _ (t ^ (i : ℕ))) := by
    rw [chartForm, gPoly, Polynomial.eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow,
      map_mul]
  rw [hchart, hdet, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := congrFun hdz i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  rw [mul_right_comm, mul_comm (z i), hi, zero_mul]

/-! ## Splitting off the free moments -/

section Split

variable {j : ℕ}

/-- `Fin N ≃ Fin (j + r) ⊕ Fin (N - (j + r))`: the constrained and the free moments. -/
def momentSplit (hj : j + r ≤ N) : Fin N ≃ Fin (j + r) ⊕ Fin (N - (j + r)) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

theorem momentSplit_lt (hj : j + r ≤ N) {n : Fin N} (hn : (n : ℕ) < j + r) :
    momentSplit hj n = Sum.inl ⟨n, hn⟩ := by
  rw [momentSplit, Equiv.trans_apply, Equiv.symm_apply_eq]
  ext
  simp

theorem momentSplit_ge (hj : j + r ≤ N) {n : Fin N} (hn : j + r ≤ (n : ℕ)) :
    momentSplit hj n = Sum.inr ⟨n - (j + r), by have := n.isLt; omega⟩ := by
  rw [momentSplit, Equiv.trans_apply, Equiv.symm_apply_eq]
  ext
  simp only [finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd]
  omega

/-- The polynomials in the free moments. -/
abbrev FreeRing (K : Type u) [Field K] (N r j : ℕ) := MvPolynomial (Fin (N - (j + r))) K

variable (K) in
/-- **`K[x_0, …, x_{N-1}] ≅ R[x_0, …, x_{j+r-1}]`**, `R` the polynomials in the free moments. -/
noncomputable def splitEquiv (hj : j + r ≤ N) :
    MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin (j + r)) (FreeRing K N r j) :=
  (MvPolynomial.renameEquiv K (momentSplit hj)).trans
    (MvPolynomial.sumAlgEquiv K (Fin (j + r)) (Fin (N - (j + r))))

theorem splitEquiv_X_lt (hj : j + r ≤ N) {n : Fin N} (hn : (n : ℕ) < j + r) :
    splitEquiv K hj (MvPolynomial.X n) = MvPolynomial.X ⟨n, hn⟩ := by
  simp [splitEquiv, momentSplit_lt hj hn]

theorem splitEquiv_X_ge (hj : j + r ≤ N) {n : Fin N} (hn : j + r ≤ (n : ℕ)) :
    splitEquiv K hj (MvPolynomial.X n)
      = MvPolynomial.C (MvPolynomial.X ⟨n - (j + r), by have := n.isLt; omega⟩) := by
  simp [splitEquiv, momentSplit_ge hj hn]

theorem splitEquiv_minor (hj : j + r ≤ N) {c : Fin (r + 1) → ℕ} (hbound : ∀ i, r + 1 + c i ≤ N)
    (hc : ∀ i, c i < j) :
    splitEquiv K hj (RHTower.finiteHankelMaximalMinorOver K c hbound)
      = RHTower.finiteHankelMaximalMinorOver (FreeRing K N r j) c
          (fun i => by have := hc i; omega) := by
  rw [RHTower.finiteHankelMaximalMinorOver, RHTower.finiteHankelMaximalMinorOver, AlgEquiv.map_det]
  congr 1
  ext i i'
  simp only [AlgEquiv.mapMatrix_apply, Matrix.map_apply]
  rw [splitEquiv_X_lt hj (by
    simp only [RHTower.finiteHankelIndex]; have := i.isLt; have := hc i'; omega)]
  rfl

/-- **The free moments split off**: `secantIdealUpTo` is the secant ideal over `R`. -/
theorem map_splitEquiv_secantIdealUpTo (hj : j + r ≤ N) :
    (secantIdealUpTo K N r j).map (splitEquiv K hj)
      = RHTower.finiteHankelSecantIdeal (FreeRing K N r j) (j + r) r := by
  rw [secantIdealUpTo, Ideal.map_span, RHTower.finiteHankelSecantIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨c, hb, hmono, hc, rfl⟩, rfl⟩
    exact ⟨c, _, hmono, (splitEquiv_minor hj hb hc).trans rfl⟩
  · rintro ⟨c, hb, hmono, rfl⟩
    refine ⟨_, ⟨c, fun i => by have := hb i; omega, hmono, fun i => by have := hb i; omega, rfl⟩, ?_⟩
    exact splitEquiv_minor hj (fun i => by have := hb i; omega) (fun i => by have := hb i; omega)

theorem mem_secantIdealUpTo_iff (hj : j + r ≤ N) (P : MvPolynomial (Fin N) K) :
    P ∈ secantIdealUpTo K N r j
      ↔ splitEquiv K hj P ∈ RHTower.finiteHankelSecantIdeal (FreeRing K N r j) (j + r) r := by
  rw [← map_splitEquiv_secantIdealUpTo hj, ← Ideal.mem_comap,
    Ideal.comap_map_of_bijective _ (splitEquiv K hj).bijective]

theorem secantIdealUpTo_isPrime (hj : j + r ≤ N) : (secantIdealUpTo K N r j).IsPrime := by
  have h := RHTower.finiteHankelSecantIdeal_isPrime (FreeRing K N r j) (j + r) r
  have heq : secantIdealUpTo K N r j
      = (RHTower.finiteHankelSecantIdeal (FreeRing K N r j) (j + r) r).comap (splitEquiv K hj) := by
    ext P
    rw [mem_secantIdealUpTo_iff hj, Ideal.mem_comap]
  rw [heq]
  exact Ideal.comap_isPrime _ _

end Split

/-! ## The atom parametrization over the free moments -/

section Atom

variable {j : ℕ}

/-- The polynomial `∏_l (X - t_l)` with roots the atoms. -/
noncomputable def atomPoly (R : Type u) [CommRing R] (r : ℕ) : (MvPolynomial (Fin r × Fin 2) R)[X] :=
  ∏ l : Fin r, (X - C (MvPolynomial.X (l, (1 : Fin 2))))

theorem natDegree_atomPoly_le (R : Type u) [CommRing R] [Nontrivial R] :
    (atomPoly R r).natDegree ≤ r := by
  refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun l _ => natDegree_X_sub_C _]
  simp

theorem atomPoly_eval_atom (R : Type u) [CommRing R] (l : Fin r) :
    (atomPoly R r).eval (MvPolynomial.X (l, (1 : Fin 2))) = 0 := by
  rw [atomPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [eval_sub, eval_X, eval_C, sub_self])

variable (K r N) in
/-- **The atom parametrization of the incidence ring over the free moments**:
`z_i ↦ coeff_i ∏_l (X - t_l)`, `v_n ↦ ∑_l c_l t_l^n` (`n < j + r`), `v_n ↦ x_n` (`n ≥ j + r`). -/
noncomputable def atomParam (hj : j + r ≤ N) :
    IncRing K r N →ₐ[K] MvPolynomial (Fin r × Fin 2) (FreeRing K N r j) :=
  MvPolynomial.aeval (Sum.elim (fun i => (atomPoly (FreeRing K N r j) r).coeff (i : ℕ))
    (fun n => RHTower.finiteHankelSecantParameterization (FreeRing K N r j) (j + r) r
      (splitEquiv K hj (MvPolynomial.X n))))

theorem atomParam_zv (hj : j + r ≤ N) (i : Fin (r + 1)) :
    atomParam K r N hj (zv K r N i) = (atomPoly (FreeRing K N r j) r).coeff (i : ℕ) := by
  simp [atomParam, zv]

theorem atomParam_vv_lt (hj : j + r ≤ N) {n : Fin N} (hn : (n : ℕ) < j + r) :
    atomParam K r N hj (vv K r N n) = RHTower.deningerHankelSecantMoment (FreeRing K N r j) r n := by
  rw [vv, atomParam, MvPolynomial.aeval_X, Sum.elim_inr, splitEquiv_X_lt hj hn,
    RHTower.finiteHankelSecantParameterization_X]

/-- **The atom parametrization kills every Hankel equation of `B_j`.** -/
theorem atomParam_hankelEq (hj : j + r ≤ N) {m : ℕ} (hm : m < j) :
    atomParam K r N hj (hankelEq K r N m) = 0 := by
  rw [hankelEq_eq, map_sum]
  have hterm : ∀ i : Fin (r + 1), atomParam K r N hj (zv K r N i * vAt K r N (i + m))
      = ∑ l : Fin r, MvPolynomial.X (l, (0 : Fin 2)) * MvPolynomial.X (l, (1 : Fin 2)) ^ m
          * ((atomPoly (FreeRing K N r j) r).coeff (i : ℕ) * MvPolynomial.X (l, (1 : Fin 2)) ^ (i : ℕ)) := by
    intro i
    rw [map_mul, atomParam_zv, vAt, dif_pos (by omega),
      atomParam_vv_lt hj (show ((⟨i + m, by omega⟩ : Fin N) : ℕ) < j + r by simp only; omega),
      RHTower.deningerHankelSecantMoment, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← Finset.mul_sum]
  have hev : ∑ i : Fin (r + 1), (atomPoly (FreeRing K N r j) r).coeff (i : ℕ)
        * MvPolynomial.X (l, (1 : Fin 2)) ^ (i : ℕ)
      = (atomPoly (FreeRing K N r j) r).eval (MvPolynomial.X (l, (1 : Fin 2))) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_atomPoly_le _))]
    exact Fin.sum_univ_eq_sum_range (fun i => (atomPoly (FreeRing K N r j) r).coeff i *
      MvPolynomial.X (l, (1 : Fin 2)) ^ i) (r + 1)
  rw [hev, atomPoly_eval_atom, mul_zero]

theorem atomParam_mem_hankelIdeal (hj : j + r ≤ N) {x : IncRing K r N}
    (hx : x ∈ hankelIdeal K r N j) : atomParam K r N hj x = 0 := by
  have hle : hankelIdeal K r N j ≤ RingHom.ker (atomParam K r N hj).toRingHom := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    exact atomParam_hankelEq hj hm
  exact hle hx

theorem chartForm_zero_eq : chartForm K r N 0 = zv K r N 0 := by
  rw [chartForm, map_zero, ← coeff_zero_eq_eval_zero, gPoly_coeff, dif_pos (Nat.succ_pos r)]
  rfl

theorem atomParam_chartForm_zero_ne_zero (hj : j + r ≤ N) :
    atomParam K r N hj (chartForm K r N 0) ≠ 0 := by
  rw [chartForm_zero_eq, atomParam_zv, Fin.val_zero, coeff_zero_eq_eval_zero, atomPoly, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun l _ => ?_
  simp [MvPolynomial.X_ne_zero]

theorem finiteHankelSecantParameterization_C {R : Type u} [CommRing R] (n : ℕ) (a : R) :
    RHTower.finiteHankelSecantParameterization R n r (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [RHTower.finiteHankelSecantParameterization, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, MvPolynomial.rename_C, RHTower.deningerHankelSecantParameterization,
    MvPolynomial.eval₂Hom_C]

theorem atomParam_momentEmbed (hj : j + r ≤ N) (P : MvPolynomial (Fin N) K) :
    atomParam K r N hj (momentEmbed K r N P)
      = RHTower.finiteHankelSecantParameterization (FreeRing K N r j) (j + r) r (splitEquiv K hj P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h1 : splitEquiv K hj (MvPolynomial.C c)
        = MvPolynomial.C (algebraMap K (FreeRing K N r j) c) := by
      rw [← MvPolynomial.algebraMap_apply, ← AlgEquiv.commutes (splitEquiv K hj) c,
        MvPolynomial.algebraMap_eq]
    rw [h1, finiteHankelSecantParameterization_C, momentEmbed, MvPolynomial.rename_C,
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p n hp =>
    rw [map_mul, map_mul, hp, map_mul, map_mul, momentEmbed_X, vv, atomParam, MvPolynomial.aeval_X,
      Sum.elim_inr]

/-- **A moment polynomial dying on the chart `G(0) ≠ 0` of `B_j` lies in `secantIdealUpTo`.** -/
theorem mem_secantIdealUpTo_of_chartZero (hj : j + r ≤ N) {P : MvPolynomial (Fin N) K} {m : ℕ}
    (h : chartForm K r N 0 ^ m * momentEmbed K r N P ∈ hankelIdeal K r N j) :
    P ∈ secantIdealUpTo K N r j := by
  have h1 := atomParam_mem_hankelIdeal hj h
  rw [map_mul, map_pow, atomParam_momentEmbed] at h1
  rw [mem_secantIdealUpTo_iff hj, RHTower.finiteHankelSecantIdeal_eq_parameterization_ker,
    RingHom.mem_ker]
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ (atomParam_chartForm_zero_ne_zero hj))

end Atom

end HTGeometry
