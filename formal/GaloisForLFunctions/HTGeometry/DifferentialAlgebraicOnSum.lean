import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnClosure

/-!
# Additive closure of differential algebraicity on a domain

`DifferentialAlgebraicOnClosure` records the multiplicative closure properties on an arbitrary
open, preconnected, nonempty, infinite domain.  This module adds the additive ones — constants,
sums of two functions, and finite sums — through the same meromorphic jet-field bridge.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open GaloisForLFunctions Bottcher

noncomputable section

/-- A constant satisfies the order-zero relation `y₀ − c = 0` on every set. -/
theorem differentiallyAlgebraicOn_const (U : Set ℂ) (c : ℂ) :
    DifferentiallyAlgebraicOn (fun _ : ℂ => c) U := by
  refine ⟨0, MvPolynomial.X 1 - MvPolynomial.C c, ?_, ?_⟩
  · intro h
    have hev := congrArg (MvPolynomial.eval (fun _ : Fin 2 => c + 1)) h
    simp at hev
  · intro z _
    have hval : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) (fun _ : ℂ => c) z) :
        Fin 2 → ℂ) 1 = c := by
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
      simp [iteratedDeriv_zero]
    simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, hval, sub_self]

/-- **Sums.**  Differential algebraicity on a domain is closed under addition. -/
theorem differentiallyAlgebraicOn_add {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfDA : DifferentiallyAlgebraicOn f U) (hgDA : DifferentiallyAlgebraicOn g U) :
    DifferentiallyAlgebraicOn (fun z => f z + g z) U := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := U) hUo hUc hUne
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField U) :=
    meroFieldRatFuncDifferentialAlgebra hUo hUc hUne hUinf
  letI : CharZero (meroField U) :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℂ) (meroField U)).injective
  have hsum : AnalyticOnNhd ℂ (fun z => f z + g z) U := hf.add hg
  refine (differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hsum).mp ?_
  rw [show hsum = (hf.add hg) from rfl, analyticMeroElement_add hf hg]
  exact differentialAlgebraicOver_add
    ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hf).mpr hfDA)
    ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hg).mpr hgDA)

/-- **Finite sums.**  Differential algebraicity on a domain is closed under finite sums. -/
theorem differentiallyAlgebraicOn_finsetSum {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) U)
    (hfDA : ∀ i ∈ s, DifferentiallyAlgebraicOn (f i) U) :
    DifferentiallyAlgebraicOn (fun z => ∑ i ∈ s, f i z) U := by
  classical
  induction s using Finset.induction with
  | empty => simpa using differentiallyAlgebraicOn_const U 0
  | @insert j s hj ih =>
      have hfj : AnalyticOnNhd ℂ (f j) U := hf j (Finset.mem_insert_self j s)
      have hfjDA : DifferentiallyAlgebraicOn (f j) U := hfDA j (Finset.mem_insert_self j s)
      have hrest : AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, f i z) U := by
        have hsum : (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, f i := by
          funext z
          simp [Finset.sum_apply]
        rw [hsum]
        intro z hz
        exact Finset.analyticAt_sum _ fun i hi => hf i (Finset.mem_insert_of_mem hi) z hz
      have hrestDA := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfDA i (Finset.mem_insert_of_mem hi))
      have hadd := differentiallyAlgebraicOn_add hUo hUc hUne hUinf hfj hrest hfjDA hrestDA
      have hfun : (fun z => ∑ i ∈ insert j s, f i z) = fun z => f j z + ∑ i ∈ s, f i z := by
        funext z
        rw [Finset.sum_insert hj]
      rw [hfun]
      exact hadd

/-- **Constant multiples.**  Differential algebraicity on a domain is closed under multiplication
by a scalar. -/
theorem differentiallyAlgebraicOn_const_mul {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (c : ℂ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hfDA : DifferentiallyAlgebraicOn f U) :
    DifferentiallyAlgebraicOn (fun z => c * f z) U :=
  differentiallyAlgebraicOn_mul hUo hUc hUne hUinf analyticOnNhd_const hf
    (differentiallyAlgebraicOn_const U c) hfDA


/-- **Congruence on an open domain.**  Differential algebraicity only depends on the values on an
open set.  (This restates `DifferentiallyAlgebraicOn.congr`, which is only reachable through the
`RHTower` import chain, off that stack.) -/
theorem differentiallyAlgebraicOn_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (heq : Set.EqOn f g U) (hf : DifferentiallyAlgebraicOn f U) :
    DifferentiallyAlgebraicOn g U := by
  obtain ⟨n, P, hP0, hPv⟩ := hf
  refine ⟨n, P, hP0, fun z hz => ?_⟩
  have hev : f =ᶠ[nhds z] g := by
    filter_upwards [hU.mem_nhds hz] with w hw using heq hw
  have hjet : (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g z) : Fin (n + 2) → ℂ)
      = Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
        simp only [Fin.cons_succ]
        exact (Filter.EventuallyEq.iteratedDeriv_eq (j : ℕ) hev).symm
  rw [hjet]
  exact hPv z hz

end

end GaloisForLFunctions.HTGeometry
