import GaloisForLFunctions.RHTower.SuzukiFiniteMorseResolventJetCompletion

/-!
# Uniqueness of the finite-Morse resolvent interpolant

The zero-constant Lagrange interpolant is the *only* real polynomial of degree at most the number
of nodes that vanishes at the compactification point and takes the prescribed square roots at the
nodes.

The mechanism is a root count.  Two such polynomials differ by a polynomial of degree at most `k`
vanishing at the `k + 1` distinct points `0, r_1, ..., r_k`, hence identically zero.  The extra
point is the compactification point `0`, which is distinct from every node because a below-spectrum
resolvent node never vanishes; this is exactly what the zero constant term buys.
-/

namespace RHTower

open Polynomial

noncomputable section

/-- The interpolant has degree at most the number of nodes: it is `X` times a Lagrange interpolant
of degree below the node count. -/
theorem suzukiFiniteMorseInterpolant_natDegree_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode debt : ι → ℝ) (hnode : Function.Injective resolventNode) :
    (suzukiFiniteMorseInterpolant resolventNode debt).natDegree ≤ Fintype.card ι := by
  classical
  set L := Lagrange.interpolate Finset.univ resolventNode
    (fun i => Real.sqrt (debt i) / resolventNode i) with hL
  have hdeg : L.degree < (Fintype.card ι : ℕ) := by
    have h := Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset ι)) (v := resolventNode)
      (fun i => Real.sqrt (debt i) / resolventNode i) hnode.injOn
    simpa [hL, Finset.card_univ] using h
  rcases eq_or_ne L 0 with hzero | hne
  · simp [suzukiFiniteMorseInterpolant, ← hL, hzero]
  · have hnd : L.natDegree < Fintype.card ι :=
      (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hdeg
    have hmul : (X * L : ℝ[X]).natDegree ≤ (X : ℝ[X]).natDegree + L.natDegree :=
      Polynomial.natDegree_mul_le
    have hX : (X : ℝ[X]).natDegree = 1 := Polynomial.natDegree_X
    have : (X * L : ℝ[X]).natDegree ≤ Fintype.card ι := by
      omega
    simpa [suzukiFiniteMorseInterpolant, ← hL] using this

/-- **Statement `(1)`.**  The zero-constant Lagrange interpolant is the unique real polynomial of
degree at most the node count that vanishes at the compactification point and takes the prescribed
square roots at the nodes. -/
theorem suzukiFiniteMorseInterpolant_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {resolventNode debt : ι → ℝ}
    (hnode : Function.Injective resolventNode) (hnode0 : ∀ i, resolventNode i ≠ 0)
    {p : ℝ[X]} (hdeg : p.natDegree ≤ Fintype.card ι) (h0 : p.eval 0 = 0)
    (hval : ∀ i, p.eval (resolventNode i) = Real.sqrt (debt i)) :
    p = suzukiFiniteMorseInterpolant resolventNode debt := by
  classical
  -- the node family extended by the compactification point
  set f : Option ι → ℝ := fun o => o.elim 0 resolventNode with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    match a, b with
    | none, none => rfl
    | none, some j =>
        exact absurd hab.symm (hnode0 j)
    | some i, none =>
        exact absurd hab (hnode0 i)
    | some i, some j =>
        exact congrArg some (hnode hab)
  have heval : ∀ o : Option ι,
      (p - suzukiFiniteMorseInterpolant resolventNode debt).eval (f o) = 0 := by
    intro o
    match o with
    | none =>
        simp [hf, h0, suzukiFiniteMorseInterpolant_eval_zero]
    | some i =>
        have := suzukiFiniteMorseInterpolant_eval resolventNode debt hnode hnode0 i
        simp [hf, hval i, this]
  have hcard : (p - suzukiFiniteMorseInterpolant resolventNode debt).natDegree
      < Fintype.card (Option ι) := by
    have hsub : (p - suzukiFiniteMorseInterpolant resolventNode debt).natDegree
        ≤ max p.natDegree (suzukiFiniteMorseInterpolant resolventNode debt).natDegree :=
      Polynomial.natDegree_sub_le _ _
    have hint := suzukiFiniteMorseInterpolant_natDegree_le resolventNode debt hnode
    rw [Fintype.card_option]
    omega
  have hzero : p - suzukiFiniteMorseInterpolant resolventNode debt = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hfinj heval hcard
  exact sub_eq_zero.mp hzero

/-- **Statement `(1)` for the affine Krein debts.**  On distinct below-spectrum spectral levels the
finite-Morse Krein interpolant is the unique polynomial of degree at most the level count with zero
constant term paying every exact debt. -/
theorem suzukiFiniteMorseKreinInterpolant_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {t : ι → ℝ}
    (ht : Function.Injective t) (hrho : ∀ i, rho < t i)
    {p : ℝ[X]} (hdeg : p.natDegree ≤ Fintype.card ι) (h0 : p.eval 0 = 0)
    (hval : ∀ i, p.eval (suzukiFiniteMorseResolventNode rho (t i))
      = Real.sqrt (suzukiFiniteMorseKreinDebt alpha beta (t i))) :
    p = suzukiFiniteMorseKreinInterpolant alpha beta rho t :=
  suzukiFiniteMorseInterpolant_unique
    (suzukiFiniteMorseResolventNode_injective ht)
    (fun i => suzukiFiniteMorseResolventNode_ne_zero (hrho i)) hdeg h0 hval

end

end RHTower
