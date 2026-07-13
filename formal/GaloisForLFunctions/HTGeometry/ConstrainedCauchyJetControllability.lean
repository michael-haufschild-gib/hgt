import GaloisForLFunctions.HTGeometry.PolynomialJetEscape

/-!
# Cauchy-jet controllability after a finite packet is frozen

Finitely supported real masses on an infinite injective real support control every finite Cauchy
jet packet at distinct upper-half-plane nodes.  If one disjoint packet is frozen, the target packet
remains fully controllable on the exact kernel of the frozen map: apply unconstrained
controllability to the combined packet with prescribed value `(0, target)`.

This is the finite linear-surjectivity core of the manuscript's constrained translate
transversality theorem.  It does not include the later parametric-transversality or Baire steps.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- The target Cauchy-jet control map restricted to the exact kernel of a frozen packet. -/
def constrainedCauchyJetRealLinearCombination
    {ιf ιt κ : Type*}
    (xf : ιf → ℂ) (nf : ιf → ℕ)
    (xt : ιt → ℂ) (nt : ιt → ℕ) (t : κ → ℝ) :
    LinearMap.ker (cauchyJetRealLinearCombination xf nf t) →ₗ[ℝ]
      ((Σ i, Fin (nt i)) → ℂ) :=
  (cauchyJetRealLinearCombination xt nt t).domRestrict
    (LinearMap.ker (cauchyJetRealLinearCombination xf nf t))

/-- **Finite constrained Cauchy-jet controllability.** On any infinite injective real support,
every finite target packet at distinct upper-half-plane nodes remains surjective after a disjoint
finite packet has been frozen exactly. -/
theorem constrainedCauchyJetRealLinearCombination_surjective
    {ιf ιt κ : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt] [Infinite κ]
    (xf : ιf → ℂ) (hxf : Function.Injective xf)
    (xt : ιt → ℂ) (hxt : Function.Injective xt)
    (hcross : ∀ i j, xf i ≠ xt j)
    (hupperf : ∀ i, 0 < (xf i).im) (huppert : ∀ i, 0 < (xt i).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (t : κ → ℝ) (ht : Function.Injective t) :
    Function.Surjective
      (constrainedCauchyJetRealLinearCombination xf nf xt nt t) := by
  let x : ιf ⊕ ιt → ℂ := Sum.elim xf xt
  let n : ιf ⊕ ιt → ℕ := Sum.elim nf nt
  have hx : Function.Injective x := by
    intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · exact congrArg Sum.inl (hxf hab)
    · exact False.elim (hcross i j hab)
    · exact False.elim (hcross j i hab.symm)
    · exact congrArg Sum.inr (hxt hab)
  have hupper : ∀ i, 0 < (x i).im := by
    intro i
    rcases i with i | i
    · exact hupperf i
    · exact huppert i
  have hsurj := cauchyJetRealLinearCombination_surjective x hx hupper n t ht
  intro y
  let z : (Σ i, Fin (n i)) → ℂ := fun q =>
    match q with
    | ⟨Sum.inl _, _⟩ => 0
    | ⟨Sum.inr i, j⟩ => y ⟨i, j⟩
  obtain ⟨a, ha⟩ := hsurj z
  have haf : cauchyJetRealLinearCombination xf nf t a = 0 := by
    funext q
    have hq := congrFun ha ⟨Sum.inl q.1, q.2⟩
    have heval :
        (cauchyJetRealLinearCombination x n t a) ⟨Sum.inl q.1, q.2⟩ =
          (cauchyJetRealLinearCombination xf nf t a) q := by
      simp only [cauchyJetRealLinearCombination, Finsupp.linearCombination_apply,
        Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      apply Finset.sum_congr rfl
      intro k hk
      rfl
    rw [← heval]
    simpa [z] using hq
  refine ⟨⟨a, haf⟩, ?_⟩
  funext q
  have hq := congrFun ha ⟨Sum.inr q.1, q.2⟩
  have heval :
      (cauchyJetRealLinearCombination x n t a) ⟨Sum.inr q.1, q.2⟩ =
        (cauchyJetRealLinearCombination xt nt t a) q := by
    simp only [cauchyJetRealLinearCombination, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rfl
  change (cauchyJetRealLinearCombination xt nt t a) q = y q
  rw [← heval]
  simpa [z] using hq

/-- Constrained surjectivity is invariant under invertible linear changes of coordinates on both
the frozen and target packets.  This is the formal interface for the triangular conversion from
Nevanlinna `z`-jets to parameter Cauchy jets. -/
theorem constrainedControl_surjective_of_linearEquiv
    {V J T J' T' : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup J] [Module ℝ J] [AddCommGroup T] [Module ℝ T]
    [AddCommGroup J'] [Module ℝ J'] [AddCommGroup T'] [Module ℝ T']
    (frozen : V →ₗ[ℝ] J) (target : V →ₗ[ℝ] T)
    (frozenEquiv : J ≃ₗ[ℝ] J') (targetEquiv : T ≃ₗ[ℝ] T')
    (hsurj : Function.Surjective (target.domRestrict (LinearMap.ker frozen))) :
    Function.Surjective
      ((targetEquiv.toLinearMap.comp target).domRestrict
        (LinearMap.ker (frozenEquiv.toLinearMap.comp frozen))) := by
  intro y'
  obtain ⟨v, hv⟩ := hsurj (targetEquiv.symm y')
  have hvker : (frozenEquiv.toLinearMap.comp frozen) v.1 = 0 := by
    rw [LinearMap.comp_apply, v.2, map_zero]
  refine ⟨⟨v.1, hvker⟩, ?_⟩
  change targetEquiv (target v.1) = y'
  change target v.1 = targetEquiv.symm y' at hv
  rw [hv]
  exact targetEquiv.apply_symm_apply y'

/-- A surjective control map defined on any submodule of finitely supported real masses admits
arbitrarily small positive perturbations that escape a prescribed nonzero algebraic relation. -/
theorem surjective_submodule_positive_control_escapes_mvPolynomial
    {κ σ : Type*} [Fintype σ] (S : Submodule ℝ (κ →₀ ℝ))
    (L : S →ₗ[ℝ] (σ → ℂ)) (hL : Function.Surjective L)
    (w : κ → ℝ) (hw : ∀ p, 0 < w p)
    (x : σ → ℂ) (P : MvPolynomial σ ℂ) (hP : P ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : S, ∃ ε : ℝ,
      0 < ε ∧ ε < η ∧
      (∀ p, 0 < w p + ε * (a : κ →₀ ℝ) p) ∧
      MvPolynomial.eval (x + ε • L a) P ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_mvPolynomial_eval_ne_zero hP
  obtain ⟨a, ha⟩ := hL (y - x)
  obtain ⟨ρ, hρ, hρη, hρpos⟩ :=
    exists_small_positive_finsupp_perturbation w hw (a : κ →₀ ℝ) hη
  obtain ⟨ε, hε, hερ, hne⟩ :=
    exists_small_real_line_eval_ne_zero P x y hy hρ
  refine ⟨a, ε, hε, hερ.trans hρη, ?_, ?_⟩
  · exact positive_finsupp_perturbation_of_le w hw (a : κ →₀ ℝ)
      hε.le hερ.le hρpos
  · have hcoord : x + ε • L a = fun i => x i + (ε : ℂ) * (y i - x i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [ha]
      simp
    rw [hcoord]
    exact hne

/-- **Positive algebraic escape in an exact frozen Cauchy fiber.** Every nonzero polynomial
relation on a disjoint finite target jet packet can be broken by an arbitrarily small finitely
supported real perturbation that preserves positivity and annihilates the frozen packet exactly. -/
theorem constrainedCauchyJet_positivePolynomialEscape
    {ιf ιt κ : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt] [Infinite κ]
    (xf : ιf → ℂ) (hxf : Function.Injective xf)
    (xt : ιt → ℂ) (hxt : Function.Injective xt)
    (hcross : ∀ i j, xf i ≠ xt j)
    (hupperf : ∀ i, 0 < (xf i).im) (huppert : ∀ i, 0 < (xt i).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (t : κ → ℝ) (ht : Function.Injective t)
    (w : κ → ℝ) (hw : ∀ p, 0 < w p)
    (baseJet : (Σ i, Fin (nt i)) → ℂ)
    (P : MvPolynomial (Σ i, Fin (nt i)) ℂ) (hP : P ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : LinearMap.ker (cauchyJetRealLinearCombination xf nf t), ∃ ε : ℝ,
      0 < ε ∧ ε < η ∧
      (∀ p, 0 < w p + ε * (a : κ →₀ ℝ) p) ∧
      MvPolynomial.eval
        (baseJet + ε • constrainedCauchyJetRealLinearCombination xf nf xt nt t a) P ≠ 0 := by
  exact surjective_submodule_positive_control_escapes_mvPolynomial
    (LinearMap.ker (cauchyJetRealLinearCombination xf nf t))
    (constrainedCauchyJetRealLinearCombination xf nf xt nt t)
    (constrainedCauchyJetRealLinearCombination_surjective
      xf hxf xt hxt hcross hupperf huppert nf nt t ht)
    w hw baseJet P hP hη

end
end GaloisForLFunctions.HTGeometry
