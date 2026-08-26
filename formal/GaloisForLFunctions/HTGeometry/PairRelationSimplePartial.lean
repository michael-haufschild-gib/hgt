import GaloisForLFunctions.HTGeometry.MvPolynomialGradient
import GaloisForLFunctions.HTGeometry.KaehlerKernel

/-!
# Simple partial derivatives for dependent pairs

A dependent pair containing one transcendental coordinate has a polynomial relation whose partial
derivative in the other coordinate does not vanish at the pair.  The certificate comes from a
least-total-degree relation and the universal Kähler derivation, so no denominator presentation is
required.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Algebraic dependence admits a polynomial relation with nonzero evaluated gradient. -/
theorem exists_mvPolynomial_relation_gradient_ne_zero
    {κ k K : Type*} [Field k] [Field K] [Algebra k K] [CharZero k]
    (x : κ → K) (hdep : ¬ AlgebraicIndependent k x) :
    ∃ P : MvPolynomial κ k, MvPolynomial.aeval x P = 0 ∧
      mvPolynomialGradientEval x P ≠ 0 := by
  classical
  let I : Ideal (MvPolynomial κ k) :=
    RingHom.ker (MvPolynomial.aeval x).toRingHom
  have hI : I ≠ ⊥ := by
    intro hbot
    apply hdep
    rw [algebraicIndependent_iff_ker_eq_bot]
    exact hbot
  obtain ⟨P, hPI, hP0, hmin⟩ :=
    Ideal.exists_minimal_mvPolynomial_totalDegree_ne_zero hI
  have hPeval : MvPolynomial.aeval x P = 0 := RingHom.mem_ker.mp hPI
  have hPvars : P.vars.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hvars
    have hPC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
    rw [hPC] at hPeval hP0
    have hcmap : algebraMap k K (P.coeff 0) = 0 := by
      simpa using hPeval
    have hc : P.coeff 0 = 0 := by
      apply (algebraMap k K).injective
      simpa using hcmap
    exact hP0 (by simp [hc])
  obtain ⟨i, hi⟩ := hPvars
  obtain ⟨s, hsP, his⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hpderiv0 : MvPolynomial.pderiv i P ≠ 0 :=
    pderiv_ne_zero_of_mem_support hsP his
  have hgrad : mvPolynomialGradientEval x P ≠ 0 := by
    intro hc
    have hcoeff : MvPolynomial.aeval x (MvPolynomial.pderiv i P) = 0 := by
      have h := congrArg (fun v : κ →₀ K => v i) hc
      simpa using h
    have hpI : MvPolynomial.pderiv i P ∈ I := RingHom.mem_ker.mpr hcoeff
    exact (not_lt_of_ge (hmin hpI hpderiv0))
      (totalDegree_pderiv_lt P i hpderiv0)
  exact ⟨P, hPeval, hgrad⟩

/-- If `[b,a]` is dependent and `a` is transcendental, some relation has a simple partial in the
`b` coordinate. -/
theorem exists_pair_relation_pderiv_first_ne_zero
    {k K : Type*} [Field k] [Field K] [Algebra k K] [CharZero k]
    (b a : K) (ha : Transcendental k a)
    (hdep : ¬ AlgebraicIndependent k ![b, a]) :
    ∃ P : MvPolynomial (Fin 2) k,
      MvPolynomial.aeval ![b, a] P = 0 ∧
      MvPolynomial.aeval ![b, a] (MvPolynomial.pderiv 0 P) ≠ 0 := by
  obtain ⟨P, hP, hgrad⟩ :=
    exists_mvPolynomial_relation_gradient_ne_zero ![b, a] hdep
  refine ⟨P, hP, ?_⟩
  intro hfirst
  have hdiff := derivation_aeval_eq_gradient
    (KaehlerDifferential.D k K) ![b, a] P
  rw [hP, map_zero] at hdiff
  have hDa : KaehlerDifferential.D k K a ≠ 0 := by
    intro hzero
    exact ha ((kaehlerD_eq_zero_iff_isAlgebraic).mp hzero)
  have hsecond : MvPolynomial.aeval ![b, a] (MvPolynomial.pderiv 1 P) = 0 := by
    have hsum :
        MvPolynomial.aeval ![b, a] (MvPolynomial.pderiv 0 P) •
            KaehlerDifferential.D k K b +
          MvPolynomial.aeval ![b, a] (MvPolynomial.pderiv 1 P) •
            KaehlerDifferential.D k K a = 0 := by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype,
        Fin.sum_univ_two] using hdiff.symm
    rw [hfirst, zero_smul, zero_add] at hsum
    exact (smul_eq_zero.mp hsum).resolve_right hDa
  apply hgrad
  ext i
  fin_cases i
  · simpa using hfirst
  · simpa using hsecond

/-- A dependent pair inside a larger packet has a relation supported on that pair, with a
nonvanishing partial derivative at the first selected coordinate. -/
theorem exists_relation_supported_pair_pivot
    {κ k K : Type*} [DecidableEq κ] [Field k] [Field K] [Algebra k K] [CharZero k]
    (x : κ → K) {i j : κ} (hij : i ≠ j) (hj : Transcendental k (x j))
    (hdep : ¬ AlgebraicIndependent k ![x i, x j]) :
    ∃ P : MvPolynomial κ k,
      MvPolynomial.aeval x P = 0 ∧
      MvPolynomial.aeval x (MvPolynomial.pderiv i P) ≠ 0 ∧
      ∀ l : κ, l ≠ i → l ≠ j → MvPolynomial.pderiv l P = 0 := by
  let f : Fin 2 → κ := fun r => if r = 0 then i else j
  have hf : Function.Injective f := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;> simp_all [f]
  obtain ⟨Q, hQ, hQderiv⟩ :=
    exists_pair_relation_pderiv_first_ne_zero (x i) (x j) hj hdep
  have hxf : x ∘ f = ![x i, x j] := by
    funext r
    fin_cases r <;> simp [f]
  refine ⟨MvPolynomial.rename f Q, ?_, ?_, ?_⟩
  · rw [MvPolynomial.aeval_rename, hxf]
    exact hQ
  · rw [show i = f 0 by simp [f], MvPolynomial.pderiv_rename hf,
      MvPolynomial.aeval_rename, hxf]
    exact hQderiv
  · intro l hli hlj
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hlvars
    have hlimage := MvPolynomial.vars_rename f Q hlvars
    simp only [Finset.mem_image] at hlimage
    obtain ⟨r, -, hfr⟩ := hlimage
    fin_cases r
    · exact hli (by simpa [f] using hfr.symm)
    · exact hlj (by simpa [f] using hfr.symm)

end

end GaloisForLFunctions
