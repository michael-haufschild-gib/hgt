import GaloisForLFunctions.HTGeometry.ReciprocalSourceCaustic
import GaloisForLFunctions.HTGeometry.HankelSingularLocus
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Codimension and singular loci of the source caustics (`s ≥ 1`)

The source caustic ring is the Hankel secant ring of the window with `s'` free variables adjoined,
so its dimension is `2(m - k) + s'` in the `(s' + 2m - 1)`-dimensional jet chart: the codimension
`2k - 1` transfers unchanged.  Its Zariski tangent spaces are those of the window caustic (pulled back
along the squaring automorphism) with the `s'` free directions added, so `Sing = C_{k+1}`
transfers unchanged.

* `HTGeometry.extendEquiv` : `K[x_0..x_{N-1}, y_1..y_f] / I ≃ (K[x]/I)[y]`.
* `HTGeometry.ringKrullDim_sourceRing`.
-/

namespace HTGeometry

open MvPolynomial

variable {K : Type} [Field K]

/-! ## Adjoining free variables -/

variable (K) in
/-- `K[x_0, …, x_{N-1}, y_1, …, y_f] ≅ K[x][y]`, the `y` outside. -/
noncomputable def freeVarEquiv (N f : ℕ) :
    MvPolynomial (Fin (N + f)) K ≃ₐ[K] MvPolynomial (Fin f) (MvPolynomial (Fin N) K) :=
  ((renameEquiv K finSumFinEquiv.symm).trans (renameEquiv K (Equiv.sumComm _ _))).trans
    (sumAlgEquiv K (Fin f) (Fin N))

theorem freeVarEquiv_comp_castAdd (N f : ℕ) :
    ((freeVarEquiv K N f).toRingEquiv : MvPolynomial (Fin (N + f)) K →+* MvPolynomial (Fin f) (MvPolynomial (Fin N) K)).comp
      (rename (Fin.castAdd f)).toRingHom
      = MvPolynomial.C := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun n => ?_)
  · change freeVarEquiv K N f (rename (Fin.castAdd f) (C c)) = _
    rw [rename_C, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, MvPolynomial.algebraMap_apply]
    rfl
  · change freeVarEquiv K N f (rename (Fin.castAdd f) (X n)) = _
    simp [freeVarEquiv]

theorem map_freeVarEquiv (N f : ℕ) (I : Ideal (MvPolynomial (Fin N) K)) :
    (I.map (rename (Fin.castAdd f))).map
      ((freeVarEquiv K N f).toRingEquiv : MvPolynomial (Fin (N + f)) K →+* MvPolynomial (Fin f) (MvPolynomial (Fin N) K))
      = I.map MvPolynomial.C := by
  change (I.map (rename (Fin.castAdd f)).toRingHom).map _ = _
  rw [Ideal.map_map, freeVarEquiv_comp_castAdd]

variable (K) in
/-- **Adjoining free variables to a quotient.** -/
noncomputable def extendEquiv (N f : ℕ) (I : Ideal (MvPolynomial (Fin N) K)) :
    (MvPolynomial (Fin (N + f)) K ⧸ I.map (rename (Fin.castAdd f)))
      ≃+* MvPolynomial (Fin f) (MvPolynomial (Fin N) K ⧸ I) :=
  (Ideal.quotientEquiv _ _ (freeVarEquiv K N f).toRingEquiv (map_freeVarEquiv N f I).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin f) I).symm.toRingEquiv

theorem ringKrullDim_extend (N f : ℕ) (I : Ideal (MvPolynomial (Fin N) K)) :
    ringKrullDim (MvPolynomial (Fin (N + f)) K ⧸ I.map (rename (Fin.castAdd f)))
      = ringKrullDim (MvPolynomial (Fin N) K ⧸ I) + f := by
  rw [ringKrullDim_eq_of_ringEquiv (extendEquiv K N f I), MvPolynomial.ringKrullDim_of_isNoetherianRing,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## The codimension of the source caustics -/

/-- **The source caustic has dimension `2(m - k) + s'`**: codimension `2k - 1` in the jet chart. -/
theorem ringKrullDim_sourceRing [CharZero K] {s' m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    ringKrullDim (MvPolynomial (Fin (s' + (2 * m - 1))) K ⧸ sourceIdeal K s' m (m - k))
      = ((2 * (m - k) + s' : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (sourceRingEquiv K s' m (m - k) (by omega)).toRingEquiv,
    ← map_castAdd_secantIdeal _ _ _ (by omega), ringKrullDim_extend,
    GaloisForLFunctions.HTGeometry.ringKrullDim_hankelSecantRing K (by omega)]
  push_cast
  rfl

/-! ## Zariski tangent spaces -/

section Tangent

open GaloisForLFunctions.HTGeometry

theorem tangentDeriv_mul' {n : ℕ} (p v : Fin n → K) (a b : MvPolynomial (Fin n) K) :
    tangentDeriv p v (a * b) = eval p a * tangentDeriv p v b + eval p b * tangentDeriv p v a := by
  simp only [tangentDeriv, Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun x _ => by ring

theorem tangentDeriv_add' {n : ℕ} (p v : Fin n → K) (a b : MvPolynomial (Fin n) K) :
    tangentDeriv p v (a + b) = tangentDeriv p v a + tangentDeriv p v b := by
  simp only [tangentDeriv, map_add, mul_add, Finset.sum_add_distrib]

theorem tangentDeriv_zero' {n : ℕ} (p v : Fin n → K) : tangentDeriv p v 0 = 0 := by
  simp [tangentDeriv]

/-- At a zero of `I.map φ`, the tangent conditions only need the images of `I`. -/
theorem mem_zariskiTangent_map_iff {a b : ℕ} {F : Type*} [FunLike F (MvPolynomial (Fin a) K)
    (MvPolynomial (Fin b) K)] [RingHomClass F (MvPolynomial (Fin a) K) (MvPolynomial (Fin b) K)]
    (φ : F) (I : Ideal (MvPolynomial (Fin a) K)) {p v : Fin b → K}
    (hp : ∀ g ∈ I.map φ, eval p g = 0) :
    v ∈ zariskiTangent (I.map φ) p ↔ ∀ g ∈ I, tangentDeriv p v (φ g) = 0 := by
  constructor
  · exact fun h g hg => h _ (Ideal.mem_map_of_mem _ hg)
  · intro h g hg
    rw [Ideal.map, Ideal.span, Submodule.mem_span] at hg
    let S : Submodule (MvPolynomial (Fin b) K) (MvPolynomial (Fin b) K) :=
      { carrier := {x | x ∈ I.map φ ∧ tangentDeriv p v x = 0}
        add_mem' := fun hx hy => ⟨Ideal.add_mem _ hx.1 hy.1, by rw [tangentDeriv_add', hx.2, hy.2,
          add_zero]⟩
        zero_mem' := ⟨Ideal.zero_mem _, tangentDeriv_zero' p v⟩
        smul_mem' := fun c x hx => ⟨Ideal.mul_mem_left _ c hx.1, by
          rw [smul_eq_mul, tangentDeriv_mul', hx.2, hp x hx.1, mul_zero, zero_mul, add_zero]⟩ }
    have hle : φ '' (I : Set _) ⊆ S := by
      rintro _ ⟨g', hg', rfl⟩
      exact ⟨Ideal.mem_map_of_mem _ hg', h g' hg'⟩
    exact (hg S hle).2

/-- Renaming variables: the chain rule. -/
theorem tangentDeriv_rename {a b : ℕ} (f : Fin a → Fin b) (p v : Fin b → K)
    (g : MvPolynomial (Fin a) K) :
    eval p (rename f g) = eval (p ∘ f) g ∧ tangentDeriv p v (rename f g) = tangentDeriv (p ∘ f) (v ∘ f) g := by
  have h := aeval_dualNumberPoint p v (rename f g)
  rw [aeval_rename] at h
  have h' : dualNumberPoint p v ∘ f = dualNumberPoint (p ∘ f) (v ∘ f) := rfl
  rw [h', aeval_dualNumberPoint] at h
  exact ⟨by simpa using (congrArg TrivSqZeroExt.fst h).symm,
    by simpa using (congrArg TrivSqZeroExt.snd h).symm⟩

/-- **A surjection pulls a subspace back to one of dimension raised by the kernel.** -/
theorem finrank_comap_of_surjective {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (L : V →ₗ[K] W) (hL : Function.Surjective L)
    (U : Submodule K W) :
    Module.finrank K (U.comap L) = Module.finrank K U + Module.finrank K (LinearMap.ker L) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (L.domRestrict (U.comap L))
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq_of_surjective hL, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe (fun x hx => by
      rw [Submodule.mem_comap, LinearMap.mem_ker.mp hx]; exact U.zero_mem)).finrank_eq] at h1
  exact h1.symm

variable (K) in
/-- Restriction of a jet direction to the window. -/
def windowRestrict (s' N : ℕ) : (Fin (s' + N) → K) →ₗ[K] (Fin N → K) where
  toFun v := v ∘ Fin.natAdd s'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem windowRestrict_surjective (s' N : ℕ) : Function.Surjective (windowRestrict K s' N) := by
  intro w
  refine ⟨fun q => if h : s' ≤ (q : ℕ) then w ⟨q - s', by have := q.isLt; omega⟩ else 0, ?_⟩
  funext n
  simp only [windowRestrict, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Fin.val_natAdd]
  rw [dif_pos (by omega)]
  congr 1
  ext
  simp

theorem finrank_ker_windowRestrict (s' N : ℕ) :
    Module.finrank K (LinearMap.ker (windowRestrict K s' N)) = s' := by
  have h := LinearMap.finrank_range_add_finrank_ker (windowRestrict K s' N)
  rw [LinearMap.range_eq_top.mpr (windowRestrict_surjective s' N), finrank_top,
    Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

/-- **The tangent map of an automorphism is a linear isomorphism.** -/
noncomputable def tangentEquiv {n : ℕ} (σ : MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K)
    (p : Fin n → K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (tangentMap σ.toAlgHom p) (tangentMap σ.symm.toAlgHom (mapPoint σ.toAlgHom p))
    (LinearMap.ext fun w => by
      have h := tangentMap_symm_comp σ.symm (mapPoint σ.toAlgHom p) w
      rw [AlgEquiv.symm_symm, mapPoint_symm] at h
      exact h)
    (LinearMap.ext fun v => tangentMap_symm_comp σ p v)

end Tangent

/-! ## The singular loci of the source caustics -/

section Sing

open GaloisForLFunctions.HTGeometry

variable [CharZero K]

theorem eval_sourceGen {s' m : ℕ} (z : Fin (s' + (2 * m - 1)) → K) (g : MvPolynomial (Fin (2 * m - 1)) K) :
    eval z (jetSqEquiv K (s' + (2 * m - 1)) (windowEmbed K s' m g))
      = eval (mapPoint (jetSqEquiv K (s' + (2 * m - 1))).toAlgHom z ∘ Fin.natAdd s') g := by
  have h := (tangentDeriv_map (jetSqEquiv K (s' + (2 * m - 1))).toAlgHom z 0 (windowEmbed K s' m g)).1
  simp only [AlgEquiv.coe_toAlgHom] at h
  rw [h, windowEmbed, (tangentDeriv_rename (Fin.natAdd s') _ 0 g).1]
  rfl

theorem tangentDeriv_sourceGen {s' m : ℕ} (z v : Fin (s' + (2 * m - 1)) → K)
    (g : MvPolynomial (Fin (2 * m - 1)) K) :
    tangentDeriv z v (jetSqEquiv K (s' + (2 * m - 1)) (windowEmbed K s' m g))
      = tangentDeriv (mapPoint (jetSqEquiv K (s' + (2 * m - 1))).toAlgHom z ∘ Fin.natAdd s')
          (windowRestrict K s' (2 * m - 1) (tangentEquiv (jetSqEquiv K (s' + (2 * m - 1))) z v)) g := by
  have h := (tangentDeriv_map (jetSqEquiv K (s' + (2 * m - 1))).toAlgHom z v (windowEmbed K s' m g)).2
  simp only [AlgEquiv.coe_toAlgHom] at h
  rw [h, windowEmbed, (tangentDeriv_rename (Fin.natAdd s') _ _ g).2]
  rfl

/-- The window point of `z`: the coefficients `h_{s'+1+n}` of `Z(z)²`. -/
noncomputable def windowPoint {s' m : ℕ} (z : Fin (s' + (2 * m - 1)) → K) : Fin (2 * m - 1) → K :=
  mapPoint (jetSqEquiv K (s' + (2 * m - 1))).toAlgHom z ∘ Fin.natAdd s'

theorem zero_sourceIdeal_iff {s' m r : ℕ} (z : Fin (s' + (2 * m - 1)) → K) :
    (∀ g ∈ sourceIdeal K s' m r, eval z g = 0)
      ↔ ∀ g ∈ RHTower.finiteHankelSecantIdeal K (2 * m - 1) r, eval (windowPoint z) g = 0 := by
  constructor
  · intro h g hg
    rw [windowPoint, ← eval_sourceGen]
    exact h _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg))
  · intro h g hg
    have h1 : (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (windowEmbed K s' m)
        ≤ (RingHom.ker (eval z)).comap (jetSqEquiv K (s' + (2 * m - 1))) :=
      Ideal.map_le_iff_le_comap.mpr fun x hx => by
        rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, eval_sourceGen]
        exact h x hx
    exact (Ideal.map_le_iff_le_comap.mpr h1) hg

/-- **The tangent spaces of the source caustic are those of the window caustic, pulled back.** -/
theorem zariskiTangent_sourceIdeal {s' m r : ℕ} (z : Fin (s' + (2 * m - 1)) → K)
    (hz : ∀ g ∈ sourceIdeal K s' m r, eval z g = 0) :
    zariskiTangent (sourceIdeal K s' m r) z
      = (zariskiTangent (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r) (windowPoint z)).comap
          ((windowRestrict K s' (2 * m - 1)).comp
            (tangentEquiv (jetSqEquiv K (s' + (2 * m - 1))) z).toLinearMap) := by
  have hzw := (zero_sourceIdeal_iff z).mp hz
  ext v
  rw [Submodule.mem_comap, sourceIdeal, mem_zariskiTangent_map_iff _ _ hz]
  change _ ↔ ∀ g ∈ RHTower.finiteHankelSecantIdeal K (2 * m - 1) r, tangentDeriv (windowPoint z) _ g = 0
  constructor
  · intro h g hg
    have := h _ (Ideal.mem_map_of_mem (windowEmbed K s' m) hg)
    rw [tangentDeriv_sourceGen] at this
    exact this
  · intro h g hg
    -- `g` lies in the window ideal; reduce to its generators
    have hy : ∀ x ∈ (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (windowEmbed K s' m),
        eval (mapPoint (jetSqEquiv K (s' + (2 * m - 1))).toAlgHom z) x = 0 := by
      intro x hx
      have h1 : (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (windowEmbed K s' m)
          ≤ RingHom.ker (eval (mapPoint (jetSqEquiv K (s' + (2 * m - 1))).toAlgHom z)) :=
        Ideal.map_le_iff_le_comap.mpr fun x hx => by
          rw [Ideal.mem_comap, RingHom.mem_ker, windowEmbed, (tangentDeriv_rename _ _ 0 x).1]
          exact hzw x hx
      exact h1 hx
    have hmem := (mem_zariskiTangent_map_iff (windowEmbed K s' m)
      (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r) hy
      (v := tangentEquiv (jetSqEquiv K (s' + (2 * m - 1))) z v)).mpr (fun g' hg' => by
        rw [windowEmbed, (tangentDeriv_rename _ _ _ g').2]
        exact h g' hg')
    have h2 := (tangentDeriv_map (jetSqEquiv K (s' + (2 * m - 1))).toAlgHom z v g).2
    simp only [AlgEquiv.coe_toAlgHom] at h2
    rw [h2]
    exact hmem g hg

theorem window_surjective {s' m : ℕ} (z : Fin (s' + (2 * m - 1)) → K) :
    Function.Surjective ((windowRestrict K s' (2 * m - 1)).comp
      (tangentEquiv (jetSqEquiv K (s' + (2 * m - 1))) z).toLinearMap) :=
  (windowRestrict_surjective s' _).comp (tangentEquiv _ z).surjective

theorem finrank_ker_window {s' m : ℕ} (z : Fin (s' + (2 * m - 1)) → K) :
    Module.finrank K (LinearMap.ker ((windowRestrict K s' (2 * m - 1)).comp
      (tangentEquiv (jetSqEquiv K (s' + (2 * m - 1))) z).toLinearMap)) = s' := by
  rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    finrank_ker_windowRestrict]

theorem sourceCaustic_smooth_iff_aux {s' m t : ℕ} (htm : 2 * (t + 1) < 2 * m - 1)
    (z : Fin (s' + (2 * m - 1)) → K) (hz : ∀ g ∈ sourceIdeal K s' m (t + 1), eval z g = 0) :
    (Module.finrank K (zariskiTangent (sourceIdeal K s' m (t + 1)) z) = 2 * (t + 1) + s'
        ↔ ∃ g ∈ sourceIdeal K s' m t, eval z g ≠ 0) ∧
      ((∀ g ∈ sourceIdeal K s' m t, eval z g = 0) →
        zariskiTangent (sourceIdeal K s' m (t + 1)) z = ⊤) := by
  have hw := (zero_sourceIdeal_iff z).mp hz
  have hsm := GaloisForLFunctions.HTGeometry.hankel_smooth_iff K (N := 2 * m - 1) (s := t)
    htm (windowPoint z) hw
  rw [zariskiTangent_sourceIdeal z hz, finrank_comap_of_surjective _ (window_surjective z),
    finrank_ker_window]
  refine ⟨?_, fun hnext => ?_⟩
  · rw [Nat.add_right_cancel_iff, hsm.1]
    constructor
    · rintro ⟨g, hg, hne⟩
      by_contra hall
      push Not at hall
      exact hne (((zero_sourceIdeal_iff z).mp hall) g hg)
    · rintro ⟨g, hg, hne⟩
      by_contra hall
      push Not at hall
      exact hne (((zero_sourceIdeal_iff z).mpr hall) g hg)
  · rw [hsm.2.1 ((zero_sourceIdeal_iff z).mp hnext), Submodule.comap_top]

/-- **`Sing(C_k) = C_{k+1}` in the source chart** (`s ≥ 1`): a point of the source caustic of
corank `≥ k` has a tangent space of dimension `dim = 2(m - k) + s'` exactly when it lies off the
next caustic; on the next caustic every direction is tangent. -/
theorem sourceCaustic_smooth_iff {s' m k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (z : Fin (s' + (2 * m - 1)) → K) (hz : ∀ g ∈ sourceIdeal K s' m (m - k), eval z g = 0) :
    (Module.finrank K (zariskiTangent (sourceIdeal K s' m (m - k)) z) = 2 * (m - k) + s'
        ↔ ∃ g ∈ sourceIdeal K s' m (m - k - 1), eval z g ≠ 0) ∧
      ((∀ g ∈ sourceIdeal K s' m (m - k - 1), eval z g = 0) →
        zariskiTangent (sourceIdeal K s' m (m - k)) z = ⊤) := by
  have h1 : m - k - 1 + 1 = m - k := by omega
  have h2 := sourceCaustic_smooth_iff_aux (s' := s') (t := m - k - 1) (by omega) z (by rwa [h1])
  rwa [h1] at h2

end Sing


end HTGeometry
