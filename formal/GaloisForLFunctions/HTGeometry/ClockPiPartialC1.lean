import GaloisForLFunctions.HTGeometry.ClockTrivariateC1

/-!
# Continuous partial derivatives in finitely many real variables

The classical theorem that a function with continuous partial derivatives is totally differentiable
is available in mathlib for two factors only (`hasStrictFDerivAt_uncurry_coprod`). This file proves
it for a domain `Fin k → ℝ` with arbitrarily many coordinates, by induction on the number of
coordinates: the first coordinate is split off with `Fin.cons`, the remaining ones are handled by the
inductive hypothesis, and the two-factor theorem joins them.

The differential is the expected one, `z ↦ ∑ᵢ zⁱ ∂ᵢu`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {k : ℕ}

/-- The differential of a function of finitely many real variables, from its partial derivatives. -/
noncomputable def piToCLM (c : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj i

theorem piToCLM_apply (c z : Fin k → ℝ) : piToCLM c z = ∑ i, z i * c i := by
  simp [piToCLM, mul_comm]

theorem piToCLM_single (c : Fin k → ℝ) (i : Fin k) :
    piToCLM c (Pi.single i (1 : ℝ)) = c i := by
  rw [piToCLM_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq']

theorem piToCLM_zero (c : Fin k → ℝ) : piToCLM c 0 = 0 := map_zero _

theorem continuous_piToCLM : Continuous (piToCLM (k := k)) := by
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  exact (continuous_apply i).smul continuous_const

/-- Adjoining a first coordinate is continuous. -/
theorem continuous_consPair :
    Continuous fun v : ℝ × (Fin k → ℝ) => (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ) := by
  refine continuous_pi fun j => ?_
  refine Fin.cases ?_ ?_ j
  · simpa using continuous_fst
  · intro i
    simp only [Fin.cons_succ]
    exact (continuous_apply i).comp continuous_snd

/-- `u` has the continuous partial derivatives `D` on the open set `Ω` of `Fin k → ℝ`. -/
structure IsC1OnPi (u : (Fin k → ℝ) → ℝ) (D : Fin k → (Fin k → ℝ) → ℝ)
    (Ω : Set (Fin k → ℝ)) : Prop where
  isOpen : IsOpen Ω
  hasDeriv : ∀ x ∈ Ω, ∀ i : Fin k,
    HasDerivAt (fun a : ℝ => u (Function.update x i a)) (D i x) (x i)
  cont : ∀ i : Fin k, Continuous (D i)

/-- **A function of finitely many real variables with continuous partial derivatives is
differentiable**, with the expected differential. -/
theorem hasFDerivAt_of_isC1OnPi : ∀ (k : ℕ) (u : (Fin k → ℝ) → ℝ) (D : Fin k → (Fin k → ℝ) → ℝ)
    (Ω : Set (Fin k → ℝ)), IsC1OnPi u D Ω → ∀ x ∈ Ω,
    HasFDerivAt u (piToCLM fun i => D i x) x := by
  classical
  intro k
  induction k with
  | zero =>
    intro u D Ω _ x _
    have hconst : u = fun _ : Fin 0 → ℝ => u x := by
      funext y
      congr 1
      funext i
      exact absurd i.isLt (by omega)
    have hzero : (piToCLM fun i => D i x) = 0 := by
      simp [piToCLM]
    rw [hconst, hzero]
    exact hasFDerivAt_const _ _
  | succ k ih =>
    intro u D Ω hu x hx
    -- the function of the first coordinate and of the remaining ones
    set f : ℝ → (Fin k → ℝ) → ℝ := fun a y => u (Fin.cons a y) with hf
    set f₁ : ℝ → (Fin k → ℝ) → (ℝ →L[ℝ] ℝ) :=
      fun a y => toCLM (D 0 (Fin.cons a y)) with hf₁
    set f₂ : ℝ → (Fin k → ℝ) → ((Fin k → ℝ) →L[ℝ] ℝ) :=
      fun a y => piToCLM fun i => D i.succ (Fin.cons a y) with hf₂
    set q : ℝ × (Fin k → ℝ) := (x 0, Fin.tail x) with hq
    have hcons : (Fin.cons (x 0) (Fin.tail x) : Fin (k + 1) → ℝ) = x := Fin.cons_self_tail x
    have hΩ' : IsOpen ((fun v : ℝ × (Fin k → ℝ) => (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ)) ⁻¹' Ω) :=
      hu.isOpen.preimage continuous_consPair
    have hq' : q ∈ (fun v : ℝ × (Fin k → ℝ) => (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ)) ⁻¹' Ω := by
      show (Fin.cons q.1 q.2 : Fin (k + 1) → ℝ) ∈ Ω
      rw [hq, hcons]
      exact hx
    -- the partial derivative in the first coordinate
    have df₁ : ∀ᶠ v in nhds q, HasFDerivAt (fun a : ℝ => f a v.2) (f₁ v.1 v.2) v.1 := by
      filter_upwards [hΩ'.mem_nhds hq'] with v hv
      have hmem : (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ) ∈ Ω := hv
      have hbase := hu.hasDeriv _ hmem 0
      have hupd : (fun a : ℝ => u (Function.update (Fin.cons v.1 v.2) 0 a))
          = fun a : ℝ => f a v.2 := by
        funext a
        rw [hf]
        congr 1
        exact Fin.update_cons_zero (α := fun _ : Fin (k + 1) => ℝ) v.1 v.2 a
      rw [hupd, Fin.cons_zero] at hbase
      exact hbase.hasFDerivAt
    -- the partial derivative in the remaining coordinates, by the inductive hypothesis
    have df₂ : ∀ᶠ v in nhds q, HasFDerivAt (fun y : Fin k → ℝ => f v.1 y) (f₂ v.1 v.2) v.2 := by
      filter_upwards [hΩ'.mem_nhds hq'] with v hv
      have hmem : (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ) ∈ Ω := hv
      have hconsv : Continuous fun y : Fin k → ℝ => (Fin.cons v.1 y : Fin (k + 1) → ℝ) :=
        continuous_consPair.comp (continuous_const.prodMk continuous_id)
      have hsub : IsC1OnPi (fun y : Fin k → ℝ => u (Fin.cons v.1 y))
          (fun i y => D i.succ (Fin.cons v.1 y))
          ((fun y : Fin k → ℝ => (Fin.cons v.1 y : Fin (k + 1) → ℝ)) ⁻¹' Ω) := by
        refine ⟨hu.isOpen.preimage hconsv, ?_, fun i => (hu.cont i.succ).comp hconsv⟩
        intro y hy i
        have hmemy : (Fin.cons v.1 y : Fin (k + 1) → ℝ) ∈ Ω := hy
        have hbase := hu.hasDeriv _ hmemy i.succ
        have hupd : (fun b : ℝ => u (Function.update (Fin.cons v.1 y) i.succ b))
            = fun b : ℝ => u (Fin.cons v.1 (Function.update y i b)) := by
          funext b
          congr 1
          exact (Fin.cons_update (α := fun _ : Fin (k + 1) => ℝ) v.1 y i b).symm
        rw [hupd, Fin.cons_succ] at hbase
        exact hbase
      exact ih _ _ _ hsub v.2 hmem
    have cf₁ : ContinuousAt (fun v : ℝ × (Fin k → ℝ) => f₁ v.1 v.2) q := by
      have hcont : Continuous fun v : ℝ × (Fin k → ℝ) => D 0 (Fin.cons v.1 v.2) :=
        (hu.cont 0).comp continuous_consPair
      exact (continuous_toCLM.comp hcont).continuousAt
    have cf₂ : ContinuousAt (fun v : ℝ × (Fin k → ℝ) => f₂ v.1 v.2) q := by
      have hcont : Continuous fun v : ℝ × (Fin k → ℝ) =>
          (fun i : Fin k => D i.succ (Fin.cons v.1 v.2)) := by
        refine continuous_pi fun i => ?_
        exact (hu.cont i.succ).comp continuous_consPair
      exact (continuous_piToCLM.comp hcont).continuousAt
    have hstrict := hasStrictFDerivAt_uncurry_coprod (f := f) (f₁ := f₁) (f₂ := f₂)
      df₁ df₂ cf₁ cf₂
    -- transport along the splitting of the coordinates
    set P : (Fin (k + 1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => ℝ) 0).prod
        (ContinuousLinearMap.pi fun i : Fin k =>
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => ℝ) i.succ) with hP
    have hPapply : ∀ z : Fin (k + 1) → ℝ, P z = ((z 0, fun i : Fin k => z i.succ)) := fun _ => rfl
    have hcomp := (hstrict.hasFDerivAt).comp x (P.hasFDerivAt (x := x))
    have hfun : (↿f ∘ (P : (Fin (k + 1) → ℝ) → ℝ × (Fin k → ℝ))) = u := by
      funext z
      show u (Fin.cons (z 0) fun i : Fin k => z i.succ) = u z
      congr 1
      exact Fin.cons_self_tail z
    have hdiff : ((↿f₁ q).coprod (↿f₂ q)).comp P = piToCLM fun i => D i x := by
      refine ContinuousLinearMap.ext fun z => ?_
      have hL : (((↿f₁ q).coprod (↿f₂ q)).comp P) z
          = z 0 * D 0 x + ∑ i : Fin k, z i.succ * D i.succ x := by
        show toCLM (D 0 (Fin.cons (x 0) (Fin.tail x))) (z 0)
            + piToCLM (fun i : Fin k => D i.succ (Fin.cons (x 0) (Fin.tail x)))
              (fun i : Fin k => z i.succ)
          = z 0 * D 0 x + ∑ i : Fin k, z i.succ * D i.succ x
        rw [toCLM_apply, piToCLM_apply, hcons]
      rw [hL, piToCLM_apply, Fin.sum_univ_succ]
    rw [hfun, hdiff] at hcomp
    exact hcomp

/-- The differentiability statement, in the form the chart uses. -/
theorem differentiableAt_of_isC1OnPi {u : (Fin k → ℝ) → ℝ} {D : Fin k → (Fin k → ℝ) → ℝ}
    {Ω : Set (Fin k → ℝ)} (h : IsC1OnPi u D Ω) {x : Fin k → ℝ} (hx : x ∈ Ω) :
    DifferentiableAt ℝ u x :=
  (hasFDerivAt_of_isC1OnPi k u D Ω h x hx).differentiableAt

end GaloisForLFunctions.HTGeometry
