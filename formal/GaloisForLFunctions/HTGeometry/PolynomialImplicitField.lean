import Mathlib

/-!
# Solving a polynomial jet relation for the top derivative

A polynomial relation `P(y₀,…,y_n) = 0` whose derivative in the top variable does not vanish at a
point can be solved there for the top variable: near that point the relation is equivalent to
`y_n = Φ(y₀,…,y_{n−1})` with `Φ` locally Lipschitz.  This is the implicit-function step that turns an
implicit algebraic differential equation into the explicit form the jet-uniqueness theorems consume.

The proof is the inverse function theorem applied to `(w,u) ↦ (w, P(w,u))`, whose derivative is
invertible exactly when the derivative of `P` in `u` is nonzero.  `ImplicitLipschitzGraph` proves a
quantitative variant: there the Lipschitz graph is produced on a region where the derivative stays
near a fixed functional, a hypothesis one has to establish; here nonvanishing at a single point
suffices and the region is produced by the inverse function theorem.
-/

open Filter Topology MvPolynomial

namespace GaloisForLFunctions

variable {n : ℕ}

/-- Adjoining a last coordinate, as a continuous linear map. -/
noncomputable def snocCLM (n : ℕ) : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i : Fin (n + 1) =>
    Fin.lastCases (motive := fun _i : Fin (n + 1) => ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ)
      (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ)
      (fun j : Fin n =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
          (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)) i

@[simp] theorem snocCLM_apply (p : (Fin n → ℂ) × ℂ) :
    snocCLM n p = Fin.snoc p.1 p.2 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [snocCLM]
  · simp [snocCLM]

/-- The evaluation of a polynomial with its last variable split off. -/
noncomputable def splitEval (P : MvPolynomial (Fin (n + 1)) ℂ) : ((Fin n → ℂ) × ℂ) → ℂ :=
  fun p => MvPolynomial.eval (Fin.snoc p.1 p.2) P

theorem analyticAt_splitEval (P : MvPolynomial (Fin (n + 1)) ℂ) (p : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (splitEval P) p := by
  have h := AnalyticOnNhd.eval_continuousLinearMap (f := snocCLM n) P
  have hEq : (fun x : (Fin n → ℂ) × ℂ => MvPolynomial.eval (snocCLM n x) P) = splitEval P := by
    funext x
    rw [splitEval, snocCLM_apply]
  rw [hEq] at h
  exact h p (Set.mem_univ p)

theorem contDiffAt_splitEval (P : MvPolynomial (Fin (n + 1)) ℂ) (p : (Fin n → ℂ) × ℂ) :
    ContDiffAt ℂ 2 (splitEval P) p :=
  (analyticAt_splitEval P p).contDiffAt

/-- The derivative of the split evaluation in its last variable. -/
theorem hasDerivAt_splitEval_slice (P : MvPolynomial (Fin (n + 1)) ℂ) (w₀ : Fin n → ℂ) (u₀ : ℂ) :
    HasDerivAt (fun u : ℂ => splitEval P (w₀, u))
      ((fderiv ℂ (splitEval P) (w₀, u₀)) (0, 1)) u₀ := by
  have hG : HasFDerivAt (splitEval P) (fderiv ℂ (splitEval P) (w₀, u₀)) (w₀, u₀) :=
    ((contDiffAt_splitEval P (w₀, u₀)).differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasFDerivAt (fun _ : ℂ => w₀) (0 : ℂ →L[ℂ] (Fin n → ℂ)) u₀ := hasFDerivAt_const _ _
  have h2 : HasFDerivAt (fun u : ℂ => u) (ContinuousLinearMap.id ℂ ℂ) u₀ := hasFDerivAt_id _
  have hslice : HasFDerivAt (fun u : ℂ => ((w₀, u) : (Fin n → ℂ) × ℂ))
      (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℂ ℂ)) u₀ := h1.prodMk h2
  have hcomp : HasFDerivAt (fun u : ℂ => splitEval P (w₀, u))
      ((fderiv ℂ (splitEval P) (w₀, u₀)).comp
        (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℂ ℂ))) u₀ := hG.comp u₀ hslice
  exact hcomp.hasDerivAt

/-- The linear model of `(w,u) ↦ (w, P(w,u))` at a point where the last partial derivative is
nonzero: an invertible linear map. -/
noncomputable def implicitCLE (A : (Fin n → ℂ) →L[ℂ] ℂ) {c : ℂ} (hc : c ≠ 0) :
    ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).prod
      (A.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)
        + c • ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ))
    ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).prod
      (c⁻¹ • (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ
        - A.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ))))
    (fun p => by
      refine Prod.ext ?_ ?_
      · simp
      · simp
        field_simp)
    (fun p => by
      refine Prod.ext ?_ ?_
      · simp
      · simp
        field_simp
        ring)

@[simp] theorem implicitCLE_apply (A : (Fin n → ℂ) →L[ℂ] ℂ) {c : ℂ} (hc : c ≠ 0)
    (p : (Fin n → ℂ) × ℂ) : implicitCLE A hc p = (p.1, A p.1 + c * p.2) := by
  refine Prod.ext rfl ?_
  simp [implicitCLE]

/-- **Solving a polynomial relation for its last variable.**  Where the derivative in the last
variable does not vanish, the relation is locally the graph of a Lipschitz function. -/
theorem exists_lipschitz_implicit_of_polynomial (P : MvPolynomial (Fin (n + 1)) ℂ)
    (w₀ : Fin n → ℂ) (u₀ : ℂ)
    (hP : MvPolynomial.eval (Fin.snoc w₀ u₀) P = 0)
    (hsep : deriv (fun u : ℂ => MvPolynomial.eval (Fin.snoc w₀ u) P) u₀ ≠ 0) :
    ∃ (Φ : (Fin n → ℂ) → ℂ) (K : NNReal) (S : Set (Fin n → ℂ)),
      S ∈ nhds w₀ ∧ LipschitzOnWith K Φ S ∧ Φ w₀ = u₀ ∧
      (∀ᶠ w in nhds w₀, MvPolynomial.eval (Fin.snoc w (Φ w)) P = 0) ∧
      ∀ᶠ p : (Fin n → ℂ) × ℂ in nhds (w₀, u₀),
        MvPolynomial.eval (Fin.snoc p.1 p.2) P = 0 → p.2 = Φ p.1 := by
  classical
  set base : (Fin n → ℂ) × ℂ := (w₀, u₀) with hbase
  set D : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ := fderiv ℂ (splitEval P) base with hD
  have hslice := hasDerivAt_splitEval_slice P w₀ u₀
  have hc : D (0, 1) ≠ 0 := by
    rw [← hslice.deriv]
    exact hsep
  set A : (Fin n → ℂ) →L[ℂ] ℂ := D.comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ) with hA
  have hGs : HasStrictFDerivAt (splitEval P) D base :=
    (contDiffAt_splitEval P base).hasStrictFDerivAt (by norm_num)
  have hDsplit : ∀ p : (Fin n → ℂ) × ℂ, D p = A p.1 + D (0, 1) * p.2 := by
    intro p
    have hsum : p = ((p.1, 0) : (Fin n → ℂ) × ℂ) + ((0, p.2) : (Fin n → ℂ) × ℂ) := by
      refine Prod.ext ?_ ?_ <;> simp
    have hsmul : ((0, p.2) : (Fin n → ℂ) × ℂ) = p.2 • ((0, 1) : (Fin n → ℂ) × ℂ) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [hsum, map_add, hsmul, map_smul]
    simp [hA, smul_eq_mul, mul_comm]
  have hHL : HasStrictFDerivAt (fun p : (Fin n → ℂ) × ℂ => (p.1, splitEval P p))
      ((implicitCLE A hc : ((Fin n → ℂ) × ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ))) base := by
    have hEq : (↑(implicitCLE A hc) : ((Fin n → ℂ) × ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ))
        = (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).prod D := by
      refine ContinuousLinearMap.ext fun p => ?_
      refine Prod.ext ?_ ?_
      · show (implicitCLE A hc p).1 = p.1
        rw [implicitCLE_apply]
      · show (implicitCLE A hc p).2 = D p
        rw [implicitCLE_apply]
        exact (hDsplit p).symm
    rw [hEq]
    exact hasStrictFDerivAt_fst.prodMk hGs
  set inv := hHL.localInverse _ _ _ with hinv
  have hbaseimg : ((base.1, splitEval P base) : (Fin n → ℂ) × ℂ) = (w₀, 0) := by
    refine Prod.ext rfl ?_
    show MvPolynomial.eval (Fin.snoc base.1 base.2) P = 0
    exact hP
  have hinvbase : inv (w₀, 0) = base := by
    have h := hHL.localInverse_apply_image
    rw [hbaseimg] at h
    exact h
  obtain ⟨K, S, hS, hlip⟩ := hHL.to_localInverse.exists_lipschitzOnWith
  rw [hbaseimg] at hS
  have hcontslice : ContinuousAt (fun w : Fin n → ℂ => ((w, 0) : (Fin n → ℂ) × ℂ)) w₀ :=
    (continuous_id.prodMk continuous_const).continuousAt
  refine ⟨fun w => (inv (w, 0)).2, K, {w : Fin n → ℂ | ((w, 0) : (Fin n → ℂ) × ℂ) ∈ S},
    hcontslice.preimage_mem_nhds hS, ?_, ?_, ?_, ?_⟩
  · intro w₁ h₁ w₂ h₂
    have h := hlip h₁ h₂
    calc edist (inv (w₁, 0)).2 (inv (w₂, 0)).2
        ≤ edist (inv (w₁, 0)) (inv (w₂, 0)) := by
          rw [Prod.edist_eq]
          exact le_max_right _ _
      _ ≤ (K : ENNReal) * edist ((w₁, 0) : (Fin n → ℂ) × ℂ) ((w₂, 0) : (Fin n → ℂ) × ℂ) := h
      _ = (K : ENNReal) * edist w₁ w₂ := by
          rw [Prod.edist_eq]
          simp
  · show (inv (w₀, 0)).2 = u₀
    rw [hinvbase]
  · have hev := hHL.eventually_right_inverse
    rw [hbaseimg] at hev
    have hpull := hcontslice.tendsto.eventually hev
    filter_upwards [hpull] with w hw
    have h1 : (inv (w, 0)).1 = w := congrArg Prod.fst hw
    have h2 : splitEval P (inv (w, 0)) = 0 := congrArg Prod.snd hw
    have h2' : MvPolynomial.eval (Fin.snoc ((inv (w, 0)).1) ((inv (w, 0)).2)) P = 0 := h2
    rwa [h1] at h2'
  · have hleft := hHL.eventually_left_inverse
    filter_upwards [hleft] with p hp hzero
    have hHp : ((p.1, splitEval P p) : (Fin n → ℂ) × ℂ) = (p.1, 0) := by
      refine Prod.ext rfl ?_
      show splitEval P p = 0
      exact hzero
    rw [hHp] at hp
    exact (congrArg Prod.snd hp).symm

end GaloisForLFunctions
