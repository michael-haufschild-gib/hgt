import GaloisForLFunctions.HTGeometry.SteinmetzNevanlinnaCore
import GaloisForLFunctions.HTGeometry.SteinmetzInterpolation
import GaloisForLFunctions.HTGeometry.FirstOrderCompositionDefect
import GaloisForLFunctions.HTGeometry.MeromorphicPoleJetCertificate

/-!
# Steinmetz's reduction theorem for entire functions

Let `g` be a transcendental entire function, `F_μ` entire functions and
`h_μ(z) = H_μ(z, g(z), …, g^{(n)}(z))` with polynomials `H_μ`.

* **Satz 1.**  If `Σ_μ F_μ(g) h_μ ≡ 0` and no `F_μ` vanishes identically, there are polynomials
  `P_μ`, not all zero, with `Σ_μ P_μ(g) h_μ ≡ 0`.
* **Korollar 1.**  If `Σ_μ F_μ(g) h_μ ≡ 0` and some `h_μ ≢ 0`, there are polynomials `Q_μ`, not all
  zero, with `Σ_μ Q_μ F_μ ≡ 0`.

For Satz 1 choose `s` points `t_j` at which no `F_μ` vanishes and polynomials `P_μ` of degree `D`
with `P_μ(t_j) = c_j F_μ(t_j)` (`SteinmetzInterpolation`); then `Σ P_μ(g) h_μ` vanishes wherever `g`
takes a value `t_j`, and a margin `s − D` fixed by `n` and `deg H_μ` forces it to vanish identically
(`SteinmetzNevanlinnaCore`).  Korollar 1 eliminates one index at a time with
`G_μ = P_{μ₀} F_μ − P_μ F_{μ₀}`.

Reference: N. Steinmetz, *Über die faktorisierbaren Lösungen gewöhnlicher Differentialgleichungen*,
Math. Z. 170 (1980), Satz 1 and Korollar 1; the interpolation replaces the iterated construction of
the auxiliary functions there.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set

noncomputable section

/-- **Steinmetz's Satz 1 for entire functions.** -/
theorem exists_polynomial_relation_of_comp_relation {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) {m n : ℕ} (F : Fin (m + 1) → ℂ → ℂ)
    (hF : ∀ μ, Differentiable ℂ (F μ)) (hF0 : ∀ μ, ∃ w, F μ w ≠ 0)
    (H : Fin (m + 1) → MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : ∀ z, ∑ μ, F μ (g z) * MvPolynomial.eval (jetVector g n z) (H μ) = 0) :
    ∃ P : Fin (m + 1) → Polynomial ℂ, (∃ μ, P μ ≠ 0) ∧
      ∀ z, ∑ μ, (P μ).eval (g z) * MvPolynomial.eval (jetVector g n z) (H μ) = 0 := by
  classical
  -- the margin and the parameters
  set q : ℕ := 3 + ((n + 1) * ∑ μ, (H μ).totalDegree + 1) * 2 ^ (n + 2) with hq
  set s : ℕ := (m + 1) * (q + 1) with hs
  set D : ℕ := m * (q + 1) with hD
  have hdim : (m + 1) * s < (m + 1) * (D + 1) + s := by
    rw [hs, hD]
    nlinarith
  have hmargin : D + 4 + ((n + 1) * ∑ μ, (H μ).totalDegree + 1) * 2 ^ (n + 2) ≤ s := by
    rw [hs, hD, hq]
    nlinarith
  -- points avoiding the zeros of every `F_μ`
  set Z : Set ℂ := ⋃ μ, {w : ℂ | F μ w = 0} with hZ
  have hZc : Z.Countable :=
    Set.countable_iUnion fun μ => countable_zeroSet_of_exists_ne_zero (hF μ) (hF0 μ)
  have hinf := infinite_compl_of_countable hZc
  set emb := hinf.natEmbedding with hemb
  set t : Fin s → ℂ := fun j => (emb j : ℂ) with ht
  have htinj : Function.Injective t := by
    intro i j hij
    have h := emb.injective (Subtype.ext hij)
    exact Fin.ext (by exact_mod_cast h)
  have htZ : ∀ j μ, F μ (t j) ≠ 0 := by
    intro j μ h0
    have hmem := (emb j).2
    exact hmem (Set.mem_iUnion.mpr ⟨μ, h0⟩)
  -- interpolation
  obtain ⟨P, c, hP0, hPD, hPt⟩ := exists_polynomials_proportional_at_points hdim t
    (fun μ j => F μ (t j)) (fun j => ⟨0, htZ j 0⟩)
  refine ⟨P, hP0, ?_⟩
  -- vanishing on the level sets and the Nevanlinna core
  refine sum_eq_zero_of_vanishing_on_levels hg hgnp P hPD H t htinj hmargin ?_
  intro z j hzj
  have hrz := hrel z
  calc ∑ μ, (P μ).eval (g z) * MvPolynomial.eval (jetVector g n z) (H μ)
      = ∑ μ, c j * (F μ (g z) * MvPolynomial.eval (jetVector g n z) (H μ)) := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [hzj, hPt μ j, ← hzj]
        ring
    _ = 0 := by rw [← Finset.mul_sum, hrz, mul_zero]

/-- **Steinmetz's Satz 1 over a finite index set.** -/
theorem exists_polynomial_relation_of_comp_relation_finset {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) {n : ℕ}
    {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (F : ι → ℂ → ℂ)
    (hF : ∀ μ ∈ S, Differentiable ℂ (F μ)) (hF0 : ∀ μ ∈ S, ∃ w, F μ w ≠ 0)
    (H : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : ∀ z, ∑ μ ∈ S, F μ (g z) * MvPolynomial.eval (jetVector g n z) (H μ) = 0) :
    ∃ P : ι → Polynomial ℂ, (∃ μ ∈ S, P μ ≠ 0) ∧
      ∀ z, ∑ μ ∈ S, (P μ).eval (g z) * MvPolynomial.eval (jetVector g n z) (H μ) = 0 := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by
    have := hS.card_pos
    omega⟩
  set e : Fin (m + 1) ≃ S := (S.equivFin.trans (finCongr hm)).symm with he
  have hsum : ∀ φ : ι → ℂ, ∑ μ ∈ S, φ μ = ∑ i : Fin (m + 1), φ (e i) := by
    intro φ
    rw [← Finset.sum_coe_sort S φ]
    exact (Equiv.sum_comp e (fun x : S => φ x)).symm
  obtain ⟨P', hP'0, hP'⟩ := exists_polynomial_relation_of_comp_relation hg hgnp
    (fun i => F (e i)) (fun i => hF _ (e i).2) (fun i => hF0 _ (e i).2) (fun i => H (e i))
    (fun z => by rw [← hsum (fun μ => F μ (g z) * MvPolynomial.eval (jetVector g n z) (H μ))]
                 exact hrel z)
  refine ⟨fun μ => if h : μ ∈ S then P' (e.symm ⟨μ, h⟩) else 0, ?_, fun z => ?_⟩
  · obtain ⟨i, hi⟩ := hP'0
    refine ⟨e i, (e i).2, ?_⟩
    simp only [(e i).2, dite_true, Subtype.coe_eta, Equiv.symm_apply_apply]
    exact hi
  · rw [hsum]
    have := hP' z
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [(e i).2, dite_true, Subtype.coe_eta, Equiv.symm_apply_apply]

/-- A product with a nonzero polynomial in a nonconstant entire function vanishes only if the
other factor does. -/
theorem eq_zero_of_polynomial_comp_mul_eq_zero {g h : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (hh : Differentiable ℂ h) {P : Polynomial ℂ}
    (hP : P ≠ 0) (hPh : ∀ z, P.eval (g z) * h z = 0) (z : ℂ) : h z = 0 := by
  classical
  -- some point where `P ∘ g` does not vanish: the image of `g` is open, hence infinite
  obtain ⟨z₁, hz₁⟩ : ∃ z, P.eval (g z) ≠ 0 := by
    have hgan : AnalyticOnNhd ℂ g univ := hg.differentiableOn.analyticOnNhd isOpen_univ
    rcases hgan.is_constant_or_isOpen isPreconnected_univ with hc | hopen
    · obtain ⟨w, hw⟩ := hc
      exact absurd ⟨w, fun z => hw z (mem_univ z)⟩ hgnc
    · have himg : IsOpen (g '' univ) := hopen univ subset_rfl isOpen_univ
      have hinf : (g '' univ).Infinite :=
        infinite_of_mem_nhds (g 0) (himg.mem_nhds ⟨0, mem_univ 0, rfl⟩)
      have hfin : (P.rootSet ℂ).Finite := Polynomial.rootSet_finite P ℂ
      obtain ⟨w, hw, hwr⟩ := (hinf.sdiff hfin).nonempty
      obtain ⟨z, -, rfl⟩ := hw
      refine ⟨z, fun h0 => hwr ?_⟩
      rw [Polynomial.mem_rootSet_of_ne hP]
      simpa using h0
  -- near `z₁` the factor `h` vanishes; the identity theorem finishes
  have hcont : ContinuousAt (fun z => P.eval (g z)) z₁ :=
    (P.continuous.comp hg.continuous).continuousAt
  have hev : ∀ᶠ z in nhds z₁, h z = 0 := by
    filter_upwards [hcont.eventually_ne hz₁] with z hz
    exact (mul_eq_zero.mp (hPh z)).resolve_left hz
  have hhan : AnalyticOnNhd ℂ h univ := hh.differentiableOn.analyticOnNhd isOpen_univ
  exact hhan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z₁)
    hev (mem_univ z)

/-- **Steinmetz's Korollar 1 for entire functions.**  If `Σ_{μ ∈ S} F_μ(g) h_μ ≡ 0` with
`h_μ = H_μ(z, g, …, g^{(n)})` and some `h_μ ≢ 0`, then the `F_μ` satisfy a nontrivial linear
relation with polynomial coefficients. -/
theorem exists_polynomial_relation_outer {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) {n : ℕ} {ι : Type*} [DecidableEq ι]
    (H : ι → MvPolynomial (Fin (n + 2)) ℂ) :
    ∀ (S : Finset ι) (F : ι → ℂ → ℂ), (∀ μ, Differentiable ℂ (F μ)) →
      (∀ z, ∑ μ ∈ S, F μ (g z) * MvPolynomial.eval (jetVector g n z) (H μ) = 0) →
      (∃ μ ∈ S, ∃ z, MvPolynomial.eval (jetVector g n z) (H μ) ≠ 0) →
      ∃ Q : ι → Polynomial ℂ, (∃ μ ∈ S, Q μ ≠ 0) ∧ ∀ w, ∑ μ ∈ S, (Q μ).eval w * F μ w = 0 := by
  classical
  have hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c :=
    fun ⟨c, hc⟩ => hgnp ⟨Polynomial.C c, fun z => by simpa using hc z⟩
  have hjd : ∀ μ, Differentiable ℂ fun z => MvPolynomial.eval (jetVector g n z) (H μ) := by
    intro μ
    have hjet : ∀ i : Fin (n + 2), Differentiable ℂ (fun w => jetVector g n w i) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [jetVector]
      · simpa [jetVector] using differentiable_iteratedDeriv_entire hg j
    exact differentiable_mvPolynomial_eval_comp hjet (H μ)
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro F hF hrel hh
    -- an identically vanishing `F_μ` is itself the relation
    by_cases hzero : ∃ μ ∈ S, ∀ w, F μ w = 0
    · obtain ⟨μ, hμ, hμ0⟩ := hzero
      refine ⟨fun ν => if ν = μ then 1 else 0, ⟨μ, hμ, by simp⟩, fun w => ?_⟩
      rw [Finset.sum_eq_single μ (fun ν _ hν => by simp [hν]) (fun h => absurd hμ h)]
      simp [hμ0 w]
    push Not at hzero
    have hSne : S.Nonempty := by
      obtain ⟨μ, hμ, -⟩ := hh
      exact ⟨μ, hμ⟩
    -- Satz 1
    obtain ⟨P, ⟨μ₀, hμ₀S, hPμ₀⟩, hPrel⟩ := exists_polynomial_relation_of_comp_relation_finset hg
      hgnp S hSne F (fun μ _ => hF μ) hzero H hrel
    set S' := S.erase μ₀ with hS'
    have hS'lt : S' ⊂ S := Finset.erase_ssubset hμ₀S
    set G : ι → ℂ → ℂ := fun μ w => (P μ₀).eval w * F μ w - (P μ).eval w * F μ₀ w with hG
    have hGd : ∀ μ, Differentiable ℂ (G μ) := fun μ =>
      (((P μ₀).differentiable).mul (hF μ)).sub (((P μ).differentiable).mul (hF μ₀))
    set h : ι → ℂ → ℂ := fun μ z => MvPolynomial.eval (jetVector g n z) (H μ) with hhdef
    -- the relation for `G` over `S'`
    have hGrel : ∀ z, ∑ μ ∈ S', G μ (g z) * h μ z = 0 := by
      intro z
      have h1 := hrel z
      have h2 := hPrel z
      rw [← Finset.add_sum_erase S _ hμ₀S] at h1 h2
      have hexp : ∑ μ ∈ S', G μ (g z) * h μ z
          = (P μ₀).eval (g z) * ∑ μ ∈ S', F μ (g z) * h μ z
            - F μ₀ (g z) * ∑ μ ∈ S', (P μ).eval (g z) * h μ z := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun μ _ => ?_
        simp only [hG]
        ring
      rw [hexp]
      have e1 : ∑ μ ∈ S', F μ (g z) * h μ z = -(F μ₀ (g z) * h μ₀ z) := by
        simp only [hhdef] at h1 ⊢
        linear_combination h1
      have e2 : ∑ μ ∈ S', (P μ).eval (g z) * h μ z = -((P μ₀).eval (g z) * h μ₀ z) := by
        simp only [hhdef] at h2 ⊢
        linear_combination h2
      rw [e1, e2]
      ring
    -- some `h_μ` with `μ ∈ S'` is nonzero
    have hh' : ∃ μ ∈ S', ∃ z, h μ z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨μ, hμS, z, hz⟩ := hh
      have hμ₀zero : ∀ z, h μ₀ z = 0 := by
        refine eq_zero_of_polynomial_comp_mul_eq_zero hg hgnc (hjd μ₀) hPμ₀ fun z => ?_
        have h2 := hPrel z
        rw [← Finset.add_sum_erase S _ hμ₀S] at h2
        have hrest : ∑ μ ∈ S', (P μ).eval (g z) * h μ z = 0 :=
          Finset.sum_eq_zero fun μ hμ => by rw [hcon μ hμ z, mul_zero]
        simp only [hhdef] at hrest h2
        rw [hrest, add_zero] at h2
        exact h2
      by_cases hμμ₀ : μ = μ₀
      · subst hμμ₀
        exact hz (hμ₀zero z)
      · exact hz (hcon μ (Finset.mem_erase.mpr ⟨hμμ₀, hμS⟩) z)
    -- induction
    obtain ⟨Q', ⟨ν, hνS', hQ'ν⟩, hQ'rel⟩ :=
      ih S' hS'lt G hGd (fun z => by simpa [hhdef] using hGrel z) (by simpa [hhdef] using hh')
    refine ⟨fun μ => if μ = μ₀ then -∑ ν ∈ S', Q' ν * P ν else Q' μ * P μ₀, ⟨ν,
      (Finset.mem_erase.mp hνS').2, ?_⟩, fun w => ?_⟩
    · have hνμ₀ : ν ≠ μ₀ := (Finset.mem_erase.mp hνS').1
      simp only [hνμ₀, if_false]
      exact mul_ne_zero hQ'ν hPμ₀
    · rw [← Finset.add_sum_erase S _ hμ₀S, ← hS']
      beta_reduce
      rw [if_pos rfl]
      have hrest : ∑ μ ∈ S', (if μ = μ₀ then -∑ ν ∈ S', Q' ν * P ν else Q' μ * P μ₀).eval w
          * F μ w = ∑ μ ∈ S', (Q' μ).eval w * ((P μ₀).eval w * F μ w) := by
        refine Finset.sum_congr rfl fun μ hμ => ?_
        have hμμ₀ : μ ≠ μ₀ := (Finset.mem_erase.mp hμ).1
        simp only [hμμ₀, if_false, Polynomial.eval_mul]
        ring
      rw [hrest]
      have hQ'w := hQ'rel w
      simp only [hG] at hQ'w
      have hsplit : ∑ μ ∈ S', (Q' μ).eval w * ((P μ₀).eval w * F μ w - (P μ).eval w * F μ₀ w)
          = ∑ μ ∈ S', (Q' μ).eval w * ((P μ₀).eval w * F μ w)
            - F μ₀ w * ∑ μ ∈ S', (Q' μ).eval w * (P μ).eval w := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun μ _ => ?_
        ring
      rw [hsplit] at hQ'w
      simp only [Polynomial.eval_neg, Polynomial.eval_finsetSum, Polynomial.eval_mul]
      linear_combination hQ'w

end

end GaloisForLFunctions.HTGeometry
