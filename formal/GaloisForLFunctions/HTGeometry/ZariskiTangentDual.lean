import Mathlib

/-!
# Zariski tangent spaces of affine varieties via dual numbers

For an ideal `I ⊆ K[x_1, …, x_N]` and a point `p`, the Zariski tangent space is

`T_p(I) = {v : ∂_v g(p) = 0 for all g ∈ I}`,  `∂_v g(p) = Σ v_n (∂g/∂x_n)(p)`.

* `aeval_dualNumberPoint` — evaluation at `p + εv` over the dual numbers is `g(p) + ε ∂_v g(p)`;
* `tangentDeriv_map` — the chain rule for a substitution `σ`, read off from the dual numbers:
  `∂_v (σ g)(p) = ∂_{Mv} g(y)` with `y = σ*(p)` and `(Mv)_n = ∂_v (σ x_n)(p)`;
* `finrank_zariskiTangent_eq_of_algEquiv` — an automorphism with `σ(I) = I` identifies the tangent
  spaces at `p` and at `σ*(p)`;
* `zariskiTangent_eq_top_of_le_sqIdeal` — if `I` lies in `m_p²` every direction is tangent.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial TrivSqZeroExt

noncomputable section

variable {K : Type*} [CommRing K] {N : ℕ}

/-- The point `p + εv` over the dual numbers. -/
def dualNumberPoint (p v : Fin N → K) : Fin N → TrivSqZeroExt K K := fun n => inl (p n) + inr (v n)

/-- The directional derivative `∂_v g(p) = Σ v_n (∂g/∂x_n)(p)`. -/
def tangentDeriv (p v : Fin N → K) (g : MvPolynomial (Fin N) K) : K :=
  ∑ n, v n * eval p (pderiv n g)

theorem tangentDeriv_add_left (p v w : Fin N → K) (g : MvPolynomial (Fin N) K) :
    tangentDeriv p (v + w) g = tangentDeriv p v g + tangentDeriv p w g := by
  simp only [tangentDeriv, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem tangentDeriv_smul_left (p v : Fin N → K) (c : K) (g : MvPolynomial (Fin N) K) :
    tangentDeriv p (c • v) g = c * tangentDeriv p v g := by
  simp only [tangentDeriv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem tangentDeriv_X (p v : Fin N → K) (n : Fin N) : tangentDeriv p v (X n) = v n := by
  classical
  simp only [tangentDeriv, pderiv_X]
  rw [Finset.sum_eq_single n]
  · simp
  · intro m _ hm; simp [hm]
  · intro h; exact absurd (Finset.mem_univ n) h

/-- **Evaluation at `p + εv`.** -/
theorem aeval_dualNumberPoint (p v : Fin N → K) (g : MvPolynomial (Fin N) K) :
    aeval (dualNumberPoint p v) g = inl (eval p g) + inr (tangentDeriv p v g) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C c =>
      simp [tangentDeriv, TrivSqZeroExt.algebraMap_eq_inl]
  | add f g hf hg =>
      rw [map_add, hf, hg, map_add]
      simp only [tangentDeriv, map_add, mul_add, Finset.sum_add_distrib, inl_add, inr_add]
      abel
  | mul_X f i hf =>
      rw [map_mul, hf, aeval_X]
      refine TrivSqZeroExt.ext ?_ ?_
      · simp [dualNumberPoint]
      · simp only [dualNumberPoint, snd_mul, fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
          add_zero, zero_add, smul_eq_mul, op_smul_eq_mul, tangentDeriv, Derivation.leibniz, pderiv_X,
          map_add, map_mul, eval_X]
        have h1 : ∑ x, v x * (eval p f * eval p (Pi.single (M := fun _ => MvPolynomial (Fin N) K) x 1 i)) =
            eval p f * v i := by
          rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx])
            (by simp)]
          simp; ring
        calc eval p f * v i + (∑ n, v n * eval p (pderiv n f)) * p i
            = ∑ x, v x * (eval p f * eval p (Pi.single (M := fun _ => MvPolynomial (Fin N) K) x 1 i)) +
                ∑ x, v x * (p i * eval p (pderiv x f)) := by
              rw [h1, Finset.sum_mul]
              congr 1
              exact Finset.sum_congr rfl fun x _ => by ring
          _ = _ := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun x _ => by ring

/-- The Zariski tangent space of `V(I)` at `p`. -/
def zariskiTangent (I : Ideal (MvPolynomial (Fin N) K)) (p : Fin N → K) :
    Submodule K (Fin N → K) where
  carrier := {v | ∀ g ∈ I, tangentDeriv p v g = 0}
  add_mem' {v w} hv hw g hg := by rw [tangentDeriv_add_left, hv g hg, hw g hg, add_zero]
  zero_mem' g _ := by simp [tangentDeriv]
  smul_mem' c v hv g hg := by rw [tangentDeriv_smul_left, hv g hg, mul_zero]

theorem mem_zariskiTangent {I : Ideal (MvPolynomial (Fin N) K)} {p v : Fin N → K} :
    v ∈ zariskiTangent I p ↔ ∀ g ∈ I, tangentDeriv p v g = 0 := Iff.rfl

/-- **The chain rule**, from the dual numbers. -/
theorem tangentDeriv_map (σ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K) (p v : Fin N → K)
    (g : MvPolynomial (Fin N) K) :
    eval p (σ g) = eval (fun n => eval p (σ (X n))) g ∧
      tangentDeriv p v (σ g) =
        tangentDeriv (fun n => eval p (σ (X n))) (fun n => tangentDeriv p v (σ (X n))) g := by
  have hcomp : (aeval (dualNumberPoint p v)).comp σ =
      aeval (dualNumberPoint (fun n => eval p (σ (X n))) (fun n => tangentDeriv p v (σ (X n)))) := by
    refine MvPolynomial.algHom_ext fun n => ?_
    rw [AlgHom.comp_apply, aeval_dualNumberPoint, aeval_X]
    rfl
  have h := congrArg (fun φ : MvPolynomial (Fin N) K →ₐ[K] TrivSqZeroExt K K => φ g) hcomp
  simp only [AlgHom.comp_apply, aeval_dualNumberPoint] at h
  exact ⟨by simpa using congrArg fst h, by simpa using congrArg snd h⟩

/-- The linear map `v ↦ (∂_v (σ x_n)(p))_n`. -/
def tangentMap (σ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K) (p : Fin N → K) :
    (Fin N → K) →ₗ[K] (Fin N → K) where
  toFun v n := tangentDeriv p v (σ (X n))
  map_add' v w := by funext n; exact tangentDeriv_add_left _ _ _ _
  map_smul' c v := by funext n; exact tangentDeriv_smul_left _ _ _ _

/-- The image point `σ*(p)`. -/
def mapPoint (σ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K) (p : Fin N → K) :
    Fin N → K := fun n => eval p (σ (X n))

theorem tangentMap_symm_comp (σ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K)
    (p v : Fin N → K) :
    tangentMap σ.symm.toAlgHom (mapPoint σ.toAlgHom p) (tangentMap σ.toAlgHom p v) = v := by
  funext n
  have h := (tangentDeriv_map σ.toAlgHom p v (σ.symm (X n))).2
  simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
    tangentDeriv_X] at h
  exact h.symm

theorem mapPoint_symm (σ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K) (p : Fin N → K) :
    mapPoint σ.symm.toAlgHom (mapPoint σ.toAlgHom p) = p := by
  funext n
  have h := (tangentDeriv_map σ.toAlgHom p 0 (σ.symm (X n))).1
  simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
    eval_X] at h
  exact h.symm

/-- **An automorphism preserving `I` identifies the tangent spaces.** -/
theorem tangentMap_mem_zariskiTangent (σ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K)
    {I : Ideal (MvPolynomial (Fin N) K)} (hI : ∀ g ∈ I, σ g ∈ I) {p v : Fin N → K}
    (hv : v ∈ zariskiTangent I p) :
    tangentMap σ.toAlgHom p v ∈ zariskiTangent I (mapPoint σ.toAlgHom p) := by
  intro g hg
  have h := (tangentDeriv_map σ.toAlgHom p v g).2
  simp only [AlgEquiv.coe_toAlgHom] at h
  rw [show tangentMap σ.toAlgHom p v = fun n => tangentDeriv p v (σ (X n)) from rfl,
    show mapPoint σ.toAlgHom p = fun n => eval p (σ (X n)) from rfl, ← h]
  exact hv _ (hI g hg)

variable [Field K] in
theorem finrank_zariskiTangent_eq_of_algEquiv {K : Type*} [Field K]
    (σ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K)
    {I : Ideal (MvPolynomial (Fin N) K)} (hI : ∀ g ∈ I, σ g ∈ I) (hI' : ∀ g ∈ I, σ.symm g ∈ I)
    (p : Fin N → K) :
    Module.finrank K (zariskiTangent I p) =
      Module.finrank K (zariskiTangent I (mapPoint σ.toAlgHom p)) := by
  set y := mapPoint σ.toAlgHom p
  have hfwd : ∀ v ∈ zariskiTangent I p, tangentMap σ.toAlgHom p v ∈ zariskiTangent I y :=
    fun v hv => tangentMap_mem_zariskiTangent σ hI hv
  have hbwd : ∀ w ∈ zariskiTangent I y,
      tangentMap σ.symm.toAlgHom y w ∈ zariskiTangent I p := by
    intro w hw
    have := tangentMap_mem_zariskiTangent σ.symm hI' hw
    rwa [mapPoint_symm] at this
  have hσσ : σ.symm.symm = σ := by ext; rfl
  have hinv1 : ∀ v, tangentMap σ.symm.toAlgHom y (tangentMap σ.toAlgHom p v) = v :=
    tangentMap_symm_comp σ p
  have hinv2 : ∀ w, tangentMap σ.toAlgHom p (tangentMap σ.symm.toAlgHom y w) = w := by
    intro w
    have := tangentMap_symm_comp σ.symm y w
    rwa [hσσ, mapPoint_symm] at this
  let e : zariskiTangent I p ≃ₗ[K] zariskiTangent I y :=
    { toFun := fun v => ⟨tangentMap σ.toAlgHom p v, hfwd v v.2⟩
      invFun := fun w => ⟨tangentMap σ.symm.toAlgHom y w, hbwd w w.2⟩
      map_add' := fun v w => Subtype.ext (map_add _ _ _)
      map_smul' := fun c v => Subtype.ext (map_smul _ _ _)
      left_inv := fun v => Subtype.ext (hinv1 v)
      right_inv := fun w => Subtype.ext (hinv2 w) }
  exact e.finrank_eq

/-- The ideal `m_p²` of functions vanishing to second order at `p`. -/
def sqIdeal (p : Fin N → K) : Ideal (MvPolynomial (Fin N) K) where
  carrier := {g | eval p g = 0 ∧ ∀ n, eval p (pderiv n g) = 0}
  add_mem' {f g} hf hg := ⟨by rw [map_add, hf.1, hg.1, add_zero], fun n => by
    rw [map_add, map_add, hf.2 n, hg.2 n, add_zero]⟩
  zero_mem' := ⟨map_zero _, fun n => by simp⟩
  smul_mem' c g hg := ⟨by rw [smul_eq_mul, map_mul, hg.1, mul_zero], fun n => by
    rw [smul_eq_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      hg.1, hg.2 n, mul_zero, zero_mul, add_zero]⟩

theorem zariskiTangent_eq_top_of_le_sqIdeal {I : Ideal (MvPolynomial (Fin N) K)}
    {p : Fin N → K} (h : I ≤ sqIdeal p) : zariskiTangent I p = ⊤ := by
  rw [eq_top_iff]
  intro v _ g hg
  simp only [tangentDeriv, (h hg).2, mul_zero, Finset.sum_const_zero]

end

end GaloisForLFunctions.HTGeometry
