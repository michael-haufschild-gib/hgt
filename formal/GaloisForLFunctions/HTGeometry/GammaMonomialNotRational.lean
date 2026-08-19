import GaloisForLFunctions.HTGeometry.AnalyticCofiniteTransfer

/-!
# A nontrivial Gamma monomial is never a rational function

The base case of the linear independence of Gamma monomials.  If `∏_k Γ(s+λ_k)^{n_k}` agreed with a
rational function on a right half plane, that rational function would satisfy the shift relation
`F(z+1) = (∏_k (z+λ_k)^{n_k}) F(z)`, which `not_rational_shiftRatio_zpowShiftProd` forbids as soon
as one exponent is nonzero and the shifts are pairwise incongruent modulo `ℤ`.

The only delicate point is that the functional equation lives on a half plane, not cofinitely — the
poles of `Γ` are infinite — so the identity theorem of `AnalyticCofiniteTransfer` is used to move it
onto the cofinite filter, where the orbit-mass obstruction can see the whole orbit.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem analyticAt_shift_zpow (lam : ℂ) (n : ℤ) {s : ℂ} (h : s + lam ≠ 0) :
    AnalyticAt ℂ (fun u : ℂ => (u + lam) ^ n) s := by
  have hbase : AnalyticAt ℂ (fun u : ℂ => u + lam) s := analyticAt_id.add analyticAt_const
  rcases n with m | m
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact hbase.pow m
  · simp only [zpow_negSucc]
    exact (hbase.pow (m + 1)).inv (pow_ne_zero _ h)

theorem analyticAt_polyEval (P : Polynomial ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => Polynomial.eval w P) s :=
  (Polynomial.differentiable_aeval P).differentiableOn.analyticAt Filter.univ_mem

/-- **A nontrivial Gamma monomial is not rational.** -/
theorem not_rational_gammaMonomial {r : ℕ} (lam : Fin r → ℂ)
    (hincong : ∀ k k' : Fin r, k ≠ k' → ∀ m : ℤ, lam k - lam k' ≠ (m : ℂ))
    (n : Fin r → ℤ) (k₀ : Fin r) (hn : n k₀ ≠ 0)
    (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re →
      gammaMonomial lam n s = Polynomial.eval s P / Polynomial.eval s Q) :
    False := by
  classical
  set R : ℝ := ∑ j, |(lam j).re| with hR
  set U : Set ℂ := {s : ℂ | R < s.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set f : ℂ → ℂ := fun s => Polynomial.eval (s + 1) P / Polynomial.eval (s + 1) Q with hf
  set g : ℂ → ℂ := fun s => (∏ k, (s + lam k) ^ (n k))
    * (Polynomial.eval s P / Polynomial.eval s Q) with hg
  set S : Set ℂ := {z : ℂ | Polynomial.eval z Q = 0} ∪ {z : ℂ | Polynomial.eval (z + 1) Q = 0}
    ∪ (Set.range fun k : Fin r => -lam k) with hS
  have hshiftfin : {z : ℂ | Polynomial.eval (z + 1) Q = 0}.Finite := by
    have hpre := (Polynomial.finite_setOf_isRoot hQ).preimage
      (f := fun z : ℂ => z + 1) ((add_left_injective (1 : ℂ)).injOn)
    refine Set.Finite.subset hpre ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simpa [Set.mem_preimage, Polynomial.IsRoot] using hz
  have hSfin : S.Finite :=
    ((Polynomial.finite_setOf_isRoot hQ).union hshiftfin).union (Set.finite_range _)
  have hSmem : ∀ z ∈ Sᶜ, Polynomial.eval z Q ≠ 0 ∧ Polynomial.eval (z + 1) Q ≠ 0
      ∧ ∀ k, z + lam k ≠ 0 := by
    intro z hz
    simp only [hS, Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_setOf_eq,
      Set.mem_range, not_exists] at hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    exact ⟨h1, h2, fun k hk => h3 k (by linear_combination -hk)⟩
  have hfana : AnalyticOnNhd ℂ f Sᶜ := by
    intro z hz
    obtain ⟨-, hz2, -⟩ := hSmem z hz
    have hb : AnalyticAt ℂ (fun w : ℂ => w + 1) z := analyticAt_id.add analyticAt_const
    have hnum : AnalyticAt ℂ (fun w : ℂ => Polynomial.eval (w + 1) P) z := by
      have hc := AnalyticAt.comp (g := fun w : ℂ => Polynomial.eval w P)
        (f := fun w : ℂ => w + 1) (x := z) (analyticAt_polyEval P (z + 1)) hb
      have hrw : ((fun w : ℂ => Polynomial.eval w P) ∘ fun w : ℂ => w + 1)
          = fun w : ℂ => Polynomial.eval (w + 1) P := by funext w; rfl
      rwa [hrw] at hc
    have hden : AnalyticAt ℂ (fun w : ℂ => Polynomial.eval (w + 1) Q) z := by
      have hc := AnalyticAt.comp (g := fun w : ℂ => Polynomial.eval w Q)
        (f := fun w : ℂ => w + 1) (x := z) (analyticAt_polyEval Q (z + 1)) hb
      have hrw : ((fun w : ℂ => Polynomial.eval w Q) ∘ fun w : ℂ => w + 1)
          = fun w : ℂ => Polynomial.eval (w + 1) Q := by funext w; rfl
      rwa [hrw] at hc
    exact hnum.div hden hz2
  have hgana : AnalyticOnNhd ℂ g Sᶜ := by
    intro z hz
    obtain ⟨hz1, -, hz3⟩ := hSmem z hz
    have hprod : AnalyticAt ℂ (fun w : ℂ => ∏ k, (w + lam k) ^ (n k)) z := by
      have hprod0 : AnalyticAt ℂ (∏ k : Fin r, fun u : ℂ => (u + lam k) ^ (n k)) z :=
        Finset.analyticAt_prod _ fun k _ => analyticAt_shift_zpow (lam k) (n k) (hz3 k)
      have hfun : (∏ k : Fin r, fun u : ℂ => (u + lam k) ^ (n k))
          = fun w : ℂ => ∏ k, (w + lam k) ^ (n k) := by
        funext w
        simp [Finset.prod_apply]
      rwa [hfun] at hprod0
    exact hprod.mul ((analyticAt_polyEval P z).div (analyticAt_polyEval Q z) hz1)
  have hagree : ∀ z ∈ U ∩ Sᶜ, f z = g z := by
    intro z hz
    obtain ⟨hzU, hzS⟩ := hz
    have hzre : R < z.re := hzU
    have hz1re : R < (z + 1).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have h1 : gammaMonomial lam n (z + 1)
        = Polynomial.eval (z + 1) P / Polynomial.eval (z + 1) Q := h (z + 1) hz1re
    have h2 : gammaMonomial lam n z = Polynomial.eval z P / Polynomial.eval z Q := h z hzre
    have h3 := gammaMonomial_shift_of_re lam n hzre
    show Polynomial.eval (z + 1) P / Polynomial.eval (z + 1) Q
        = (∏ k, (z + lam k) ^ (n k)) * (Polynomial.eval z P / Polynomial.eval z Q)
    rw [← h1, h3, h2]
  have hne : (U ∩ Sᶜ).Nonempty := by
    have hUinf : U.Infinite := by
      have hmap : Set.range (fun t : ℕ => ((R + 1 + (t : ℝ) : ℝ) : ℂ)) ⊆ U := by
        rintro _ ⟨t, rfl⟩
        simp only [hU, Set.mem_setOf_eq, Complex.ofReal_re]
        have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
        linarith
      refine Set.Infinite.mono hmap (Set.infinite_range_of_injective ?_)
      intro a b hab
      have hab' : ((R + 1 + (a : ℝ) : ℝ) : ℂ) = ((R + 1 + (b : ℝ) : ℝ) : ℂ) := hab
      have h1 : (R + 1 + (a : ℝ)) = (R + 1 + (b : ℝ)) := by exact_mod_cast hab'
      have h2 : (a : ℝ) = (b : ℝ) := by linarith
      exact_mod_cast h2
    have := hUinf.sdiff hSfin
    obtain ⟨z, hz⟩ := this.nonempty
    exact ⟨z, hz.1, hz.2⟩
  obtain ⟨z₀, hz₀⟩ := hne
  have hcof := eventuallyEq_cofinite_of_analytic_compl_finite hSfin hfana hgana hUopen hz₀ hagree
  exact not_rational_shiftRatio_zpowShiftProd lam n hincong k₀ hn P Q hP hQ hcof

end

end GaloisForLFunctions.HTGeometry
