import GaloisForLFunctions.HTGeometry.SignedShiftProductLogDeriv

/-!
# No rational function has a prescribed nontrivial shift ratio

The step that turns the shift obstruction into linear independence of Gamma monomials: a rational
function cannot satisfy

`F(z+1) = (∏_k (z + λ_k)^{n_k}) · F(z)`

unless every exponent vanishes, provided the shifts are pairwise incongruent modulo `ℤ`.

Taking the logarithmic derivative of the relation turns it into
`v(z+1) − v(z) = logDeriv ρ (z)` with `v = logDeriv F`; differentiating once more produces exactly
the shift equation forbidden by `not_shiftDifference_deriv_logDeriv_zpowShiftProd`, and `deriv v`
is meromorphic with finitely many poles because `F` is rational.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem logDeriv_congr_eventually {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[nhds z] g) :
    logDeriv f z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.self_of_nhds]

/-- **No rational shift ratio.** -/
theorem not_rational_shiftRatio_zpowShiftProd {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℤ)
    (hincong : ∀ k k' : Fin r, k ≠ k' → ∀ m : ℤ, lam k - lam k' ≠ (m : ℂ))
    (k₀ : Fin r) (hn : n k₀ ≠ 0)
    (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ¬ ((fun z : ℂ => Polynomial.eval (z + 1) P / Polynomial.eval (z + 1) Q)
        =ᶠ[Filter.cofinite] fun z : ℂ =>
          (∏ k, (z + lam k) ^ (n k)) * (Polynomial.eval z P / Polynomial.eval z Q)) := by
  classical
  intro heq
  set F : ℂ → ℂ := fun z => Polynomial.eval z P / Polynomial.eval z Q with hF
  set rho : ℂ → ℂ := fun z => ∏ k, (z + lam k) ^ (n k) with hrho
  set v : ℂ → ℂ := logDeriv F with hv
  set y : ℂ → ℂ := deriv v with hy
  -- analytic ingredients
  have hPana : ∀ z : ℂ, AnalyticAt ℂ (fun w => Polynomial.eval w P) z := fun z =>
    (Polynomial.differentiable_aeval P).differentiableOn.analyticAt Filter.univ_mem
  have hQana : ∀ z : ℂ, AnalyticAt ℂ (fun w => Polynomial.eval w Q) z := fun z =>
    (Polynomial.differentiable_aeval Q).differentiableOn.analyticAt Filter.univ_mem
  have hFana : ∀ z : ℂ, Polynomial.eval z Q ≠ 0 → AnalyticAt ℂ F z := fun z hz =>
    (hPana z).div (hQana z) hz
  have hFmero : ∀ z : ℂ, MeromorphicAt F z := fun z =>
    (hPana z).meromorphicAt.div (hQana z).meromorphicAt
  have hvmero : ∀ z : ℂ, MeromorphicAt v z := by
    intro z
    have h1 : MeromorphicAt (deriv F) z := (hFmero z).deriv
    have := h1.div (hFmero z)
    simpa [hv, logDeriv] using this
  have hymero : MeromorphicOn y Set.univ := fun z _ => (hvmero z).deriv
  have hvana : ∀ z : ℂ, Polynomial.eval z P ≠ 0 → Polynomial.eval z Q ≠ 0 →
      AnalyticAt ℂ v z := by
    intro z hzP hzQ
    have hFz : F z ≠ 0 := div_ne_zero hzP hzQ
    have := ((hFana z hzQ).deriv).div (hFana z hzQ) hFz
    simpa [hv, logDeriv] using this
  have hypoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite := by
    refine Set.Finite.subset
      ((Polynomial.finite_setOf_isRoot hP).union (Polynomial.finite_setOf_isRoot hQ)) ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, Polynomial.IsRoot, not_or] at hcon
    exact hz ((hvana z hcon.1 hcon.2).deriv)
  -- the bad set
  obtain ⟨B, hB⟩ : ∃ B : Set ℂ, B.Finite ∧
      ∀ z ∉ B, Polynomial.eval (z + 1) P / Polynomial.eval (z + 1) Q
        = rho z * (Polynomial.eval z P / Polynomial.eval z Q) := by
    refine ⟨{z : ℂ | ¬ (Polynomial.eval (z + 1) P / Polynomial.eval (z + 1) Q
        = rho z * (Polynomial.eval z P / Polynomial.eval z Q))}, ?_, fun z hz => ?_⟩
    · exact Filter.eventually_cofinite.mp heq
    · by_contra hcon
      exact hz hcon
  obtain ⟨hBfin, hBeq⟩ := hB
  set bad : Set ℂ := B ∪ {z : ℂ | Polynomial.eval z P = 0} ∪ {z : ℂ | Polynomial.eval z Q = 0}
    ∪ {z : ℂ | Polynomial.eval (z + 1) P = 0} ∪ {z : ℂ | Polynomial.eval (z + 1) Q = 0}
    ∪ (Set.range fun k : Fin r => -lam k) with hbad
  have hshiftfin : ∀ R : Polynomial ℂ, R ≠ 0 → {z : ℂ | Polynomial.eval (z + 1) R = 0}.Finite := by
    intro R hR
    have h := (Polynomial.finite_setOf_isRoot hR).preimage
      (f := fun z : ℂ => z + 1) ((add_left_injective (1 : ℂ)).injOn)
    refine Set.Finite.subset h ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simpa [Set.mem_preimage, Polynomial.IsRoot] using hz
  have hbadfin : bad.Finite :=
    (((((hBfin.union (Polynomial.finite_setOf_isRoot hP)).union
      (Polynomial.finite_setOf_isRoot hQ)).union (hshiftfin P hP)).union
      (hshiftfin Q hQ)).union (Set.finite_range _))
  have hopen : IsOpen badᶜ := hbadfin.isClosed.isOpen_compl
  have hgood : ∀ z ∈ badᶜ, z ∉ B ∧ Polynomial.eval z P ≠ 0 ∧ Polynomial.eval z Q ≠ 0
      ∧ Polynomial.eval (z + 1) P ≠ 0 ∧ Polynomial.eval (z + 1) Q ≠ 0
      ∧ (∀ k, z + lam k ≠ 0) := by
    intro z hz
    simp only [hbad, Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_setOf_eq,
      Set.mem_range, not_exists] at hz
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hz
    exact ⟨h1, h2, h3, h4, h5, fun k hk => h6 k (by linear_combination -hk)⟩
  -- the shift equation for `v`
  have hstep : ∀ z ∈ badᶜ, v (z + 1) - v z = logDeriv rho z := by
    intro z hz
    obtain ⟨hzB, hzP, hzQ, hzP1, hzQ1, hzlam⟩ := hgood z hz
    have hnbhd : (fun w : ℂ => F (w + 1)) =ᶠ[nhds z] fun w : ℂ => rho w * F w := by
      have hBopen : IsOpen (Bᶜ) := hBfin.isClosed.isOpen_compl
      filter_upwards [hBopen.mem_nhds hzB] with w hw
      exact hBeq w hw
    have hFz1 : F (z + 1) ≠ 0 := div_ne_zero hzP1 hzQ1
    have hFz : F z ≠ 0 := div_ne_zero hzP hzQ
    have hrhoz : rho z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hzlam k)
    have hdF1 : DifferentiableAt ℂ F (z + 1) := (hFana (z + 1) hzQ1).differentiableAt
    have hdF : DifferentiableAt ℂ F z := (hFana z hzQ).differentiableAt
    have hdrho : DifferentiableAt ℂ rho z := by
      refine DifferentiableAt.fun_finsetProd ?_
      intro k _
      exact differentiableAt_shift_zpow (lam k) (n k) (hzlam k)
    have hleft : logDeriv (fun w : ℂ => F (w + 1)) z = v (z + 1) := by
      have hg : DifferentiableAt ℂ (fun w : ℂ => w + 1) z :=
        (differentiable_id.add_const (1 : ℂ)).differentiableAt
      have hcomp := logDeriv_comp (f := F) (g := fun w : ℂ => w + 1) (x := z) hdF1 hg
      have hrw : (F ∘ fun w : ℂ => w + 1) = fun w : ℂ => F (w + 1) := by funext w; rfl
      rw [hrw] at hcomp
      have hd1 : deriv (fun w : ℂ => w + 1) z = 1 := by
        simp
      rw [hcomp, hd1, mul_one]
    have hright : logDeriv (fun w : ℂ => rho w * F w) z = logDeriv rho z + v z :=
      logDeriv_mul z hrhoz hFz hdrho hdF
    have hcongr := logDeriv_congr_eventually hnbhd
    rw [hleft, hright] at hcongr
    linear_combination hcongr
  -- differentiate it
  have hyshift : ∀ z ∈ badᶜ, y (z + 1) - y z = deriv (logDeriv rho) z := by
    intro z hz
    obtain ⟨hzB, hzP, hzQ, hzP1, hzQ1, hzlam⟩ := hgood z hz
    have hvz : DifferentiableAt ℂ v z := (hvana z hzP hzQ).differentiableAt
    have hvz1 : DifferentiableAt ℂ v (z + 1) := (hvana (z + 1) hzP1 hzQ1).differentiableAt
    have hg : DifferentiableAt ℂ (fun w : ℂ => w + 1) z :=
      (differentiable_id.add_const (1 : ℂ)).differentiableAt
    have hshift1 : DifferentiableAt ℂ (fun w : ℂ => v (w + 1)) z := by
      have := hvz1.comp z hg
      have hrw : (v ∘ fun w : ℂ => w + 1) = fun w : ℂ => v (w + 1) := by funext w; rfl
      rwa [hrw] at this
    have hev : (fun w : ℂ => v (w + 1) - v w) =ᶠ[nhds z] fun w : ℂ => logDeriv rho w := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact hstep w hw
    have hd : deriv (fun w : ℂ => v (w + 1) - v w) z = y (z + 1) - y z := by
      rw [deriv_fun_sub hshift1 hvz, deriv_comp_add_const v 1 z]
    rw [← hd, hev.deriv_eq]
  refine not_shiftDifference_deriv_logDeriv_zpowShiftProd lam n hincong k₀ hn hymero hypoles ?_
  rw [Filter.EventuallyEq, Filter.eventually_cofinite]
  refine Set.Finite.subset hbadfin ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  by_contra hcon
  exact hz (hyshift z hcon)

end

end GaloisForLFunctions.HTGeometry
