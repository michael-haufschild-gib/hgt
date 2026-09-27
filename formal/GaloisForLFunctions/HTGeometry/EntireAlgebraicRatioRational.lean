import GaloisForLFunctions.HTGeometry.EntireBezout
import GaloisForLFunctions.HTGeometry.CascadePolynomialSharpness

/-!
# A ratio of entire functions that is algebraic over `ℂ(z)` is rational

Let `g, h` be entire, `h ≢ 0`, and suppose `x = g/h` satisfies a nonzero polynomial equation with
polynomial coefficients,

`∑_{i ≤ d} qᵢ(z) g(z)ⁱ h(z)^(d-i) = 0`.

Put `ℓ = q_d` and `G = ℓ g`.  Multiplying by `ℓ^(d-1)` makes the relation monic in `G`:

`G^d + ∑_{i<d} qᵢ ℓ^(d-1-i) Gⁱ h^(d-i) = 0`.

At every point the analytic order of `h` is at most that of `G`: if it were larger, the term `G^d`
would have strictly smaller order than every other term.  Hence `G = e h` with `e` entire
(analytic division), `e` satisfies the monic relation `e^d + ∑ qᵢ ℓ^(d-1-i) eⁱ = 0`, and an entire
function algebraic over the coordinate is a polynomial.  So `ℓ g = r h` for a polynomial `r`.

This is the analytic input of the regularity of first-order function fields: `ℂ(z)` is relatively
algebraically closed in every field of meromorphic functions on `ℂ`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Multiplying the homogeneous relation by `ℓ^(d-1)` makes it monic in `ℓ g`. -/
theorem cleared_monic_relation (q : Polynomial (Polynomial ℂ)) (hd : 1 ≤ q.natDegree)
    (g h : ℂ → ℂ)
    (hrel : ∀ z, ∑ i ∈ range (q.natDegree + 1),
      (q.coeff i).eval z * g z ^ i * h z ^ (q.natDegree - i) = 0) (z : ℂ) :
    (q.leadingCoeff.eval z * g z) ^ q.natDegree +
      ∑ i ∈ range q.natDegree,
        (q.coeff i * q.leadingCoeff ^ (q.natDegree - 1 - i)).eval z *
          (q.leadingCoeff.eval z * g z) ^ i * h z ^ (q.natDegree - i) = 0 := by
  set d := q.natDegree with hdd
  have hz := hrel z
  rw [sum_range_succ] at hz
  have hlead : q.coeff d = q.leadingCoeff := rfl
  have key : (q.leadingCoeff.eval z * g z) ^ d +
      ∑ i ∈ range d, (q.coeff i * q.leadingCoeff ^ (d - 1 - i)).eval z *
        (q.leadingCoeff.eval z * g z) ^ i * h z ^ (d - i) =
      q.leadingCoeff.eval z ^ (d - 1) *
        (∑ i ∈ range d, (q.coeff i).eval z * g z ^ i * h z ^ (d - i) +
          (q.coeff d).eval z * g z ^ d * h z ^ (d - d)) := by
    rw [mul_add, Finset.mul_sum, hlead, Nat.sub_self, pow_zero, mul_one, add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < d := Finset.mem_range.mp hi
      rw [eval_mul, eval_pow, mul_pow]
      have hpow : q.leadingCoeff.eval z ^ (d - 1) =
          q.leadingCoeff.eval z ^ (d - 1 - i) * q.leadingCoeff.eval z ^ i := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : i ≤ d - 1)]
      rw [hpow]
      ring
    · have hpow : q.leadingCoeff.eval z ^ d =
          q.leadingCoeff.eval z ^ (d - 1) * q.leadingCoeff.eval z := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      rw [mul_pow, hpow]
      ring
  rw [key, hz, mul_zero]

/-- **Order comparison.**  In a monic relation `G^d + ∑_{i<d} cᵢ Gⁱ h^(d-i) = 0` of entire
functions, the analytic order of `h` never exceeds that of `G`. -/
theorem analyticOrderAt_le_of_monic_relation {G h : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hh : Differentiable ℂ h) (d : ℕ) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ z, G z ^ d + ∑ i ∈ range d, (c i).eval z * G z ^ i * h z ^ (d - i) = 0)
    (z₀ : ℂ) : analyticOrderAt h z₀ ≤ analyticOrderAt G z₀ := by
  have hGa : ∀ z, AnalyticAt ℂ G z := fun z => hG.differentiableOn.analyticAt Filter.univ_mem
  have hha : ∀ z, AnalyticAt ℂ h z := fun z => hh.differentiableOn.analyticAt Filter.univ_mem
  have hca : ∀ (p : Polynomial ℂ) z, AnalyticAt ℂ (fun w => p.eval w) z := fun p z =>
    (Polynomial.differentiable p).differentiableOn.analyticAt Filter.univ_mem
  by_contra hlt
  push Not at hlt
  have hGtop : analyticOrderAt G z₀ ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hGtop
  have hhge : ((a + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt h z₀ := by
    rw [← ha] at hlt
    exact_mod_cast Order.add_one_le_of_lt hlt
  -- every lower term has order at least `d a + 1`
  let term : ℕ → ℂ → ℂ := fun i z => (c i).eval z * G z ^ i * h z ^ (d - i)
  have hterm : ∀ i ∈ range d, ((d * a + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (term i) z₀ := by
    intro i hi
    have hi' : i < d := Finset.mem_range.mp hi
    have hmul : term i = (fun w => (c i).eval w) * G ^ i * h ^ (d - i) := by
      funext w
      simp [term]
    rw [hmul, analyticOrderAt_mul ((hca _ _).mul ((hGa z₀).pow i)) ((hha z₀).pow _),
      analyticOrderAt_mul (hca _ _) ((hGa z₀).pow i), analyticOrderAt_pow (hGa z₀),
      analyticOrderAt_pow (hha z₀), ← ha]
    calc ((d * a + 1 : ℕ) : ℕ∞) ≤ ((i * a + (d - i) * (a + 1) : ℕ) : ℕ∞) := by
          have : d * a + 1 ≤ i * a + (d - i) * (a + 1) := by
            have hdi : d = i + (d - i) := by omega
            nth_rewrite 1 [hdi]
            have h1 : 1 ≤ d - i := by omega
            nlinarith
          exact_mod_cast this
      _ ≤ analyticOrderAt (fun w => (c i).eval w) z₀ + i • (a : ℕ∞) +
            (d - i) • analyticOrderAt h z₀ := by
          push_cast
          rw [nsmul_eq_mul, nsmul_eq_mul]
          have h2 : ((d - i : ℕ) : ℕ∞) * ((a : ℕ∞) + 1) ≤ ((d - i : ℕ) : ℕ∞) * analyticOrderAt h z₀ := by
            gcongr
            exact_mod_cast hhge
          calc (i : ℕ∞) * a + ((d - i : ℕ) : ℕ∞) * ((a : ℕ∞) + 1)
              ≤ 0 + (i : ℕ∞) * a + ((d - i : ℕ) : ℕ∞) * analyticOrderAt h z₀ := by
                rw [zero_add]
                exact add_le_add le_rfl h2
            _ ≤ _ := by gcongr; exact bot_le
  -- hence the whole lower sum does
  have hsum : ∀ s : Finset ℕ, s ⊆ range d →
      ((d * a + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z => ∑ i ∈ s, term i z) z₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp [analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall fun _ => rfl)]
    | @insert j s hj ih =>
        intro hsub
        have hfun : (fun z => ∑ i ∈ insert j s, term i z) =
            (fun z => term j z) + (fun z => ∑ i ∈ s, term i z) := by
          funext z
          simp [Finset.sum_insert hj]
        rw [hfun]
        have hja : AnalyticAt ℂ (term j) z₀ :=
          ((hca _ _).mul ((hGa z₀).pow j)).mul ((hha z₀).pow _)
        have hsa : AnalyticAt ℂ (fun z => ∑ i ∈ s, term i z) z₀ := by
          have : (fun z => ∑ i ∈ s, term i z) = ∑ i ∈ s, term i := by
            funext z; simp
          rw [this]
          exact Finset.analyticAt_sum _ fun i _ =>
            ((hca _ _).mul ((hGa z₀).pow i)).mul ((hha z₀).pow _)
        exact le_trans (le_min (hterm j (hsub (Finset.mem_insert_self j s)))
          (ih (fun x hx => hsub (Finset.mem_insert_of_mem hx)))) le_analyticOrderAt_add
  have hlow := hsum (range d) subset_rfl
  have heq : G ^ d = -(fun z => ∑ i ∈ range d, term i z) := by
    funext z
    have := hrel z
    simp only [Pi.pow_apply, Pi.neg_apply, term]
    linear_combination this
  have hGd : analyticOrderAt (G ^ d) z₀ = ((d * a : ℕ) : ℕ∞) := by
    rw [analyticOrderAt_pow (hGa z₀), ← ha]
    push_cast
    rw [nsmul_eq_mul]
  have hsumfun : (fun z => ∑ i ∈ range d, term i z) = -(G ^ d) := by
    rw [heq, neg_neg]
  rw [hsumfun, analyticOrderAt_neg, hGd] at hlow
  exact absurd hlow (by exact_mod_cast Nat.not_succ_le_self (d * a))

/-- **An algebraic ratio of entire functions is rational.**  If `g/h` satisfies a nonzero
polynomial equation over `ℂ[z]`, then `ℓ g = r h` for the leading coefficient `ℓ` and some
polynomial `r`. -/
theorem exists_polynomial_mul_eq_of_algebraic_ratio {g h : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hh : Differentiable ℂ h) (hh0 : ∃ z, h z ≠ 0) (q : Polynomial (Polynomial ℂ)) (hq : q ≠ 0)
    (hrel : ∀ z, ∑ i ∈ range (q.natDegree + 1),
      (q.coeff i).eval z * g z ^ i * h z ^ (q.natDegree - i) = 0) :
    ∃ r : Polynomial ℂ, ∀ z, q.leadingCoeff.eval z * g z = r.eval z * h z := by
  set d := q.natDegree with hdd
  -- the degree is positive
  have hd : 1 ≤ d := by
    by_contra h0
    have hd0 : d = 0 := by omega
    have hq0 : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hc0 : q.coeff 0 = 0 := by
      apply Polynomial.funext
      intro z
      have := hrel z
      rw [hd0] at this
      simpa using this
    exact hq (by rw [hq0, hc0, map_zero])
  set ℓ := q.leadingCoeff
  let G : ℂ → ℂ := fun z => ℓ.eval z * g z
  have hGd : Differentiable ℂ G := (Polynomial.differentiable ℓ).mul hg
  let c : ℕ → Polynomial ℂ := fun i => q.coeff i * ℓ ^ (d - 1 - i)
  have hmon : ∀ z, G z ^ d + ∑ i ∈ range d, (c i).eval z * G z ^ i * h z ^ (d - i) = 0 :=
    cleared_monic_relation q hd g h hrel
  obtain ⟨e, he, hGe⟩ := exists_entire_quotient hGd hh hh0
    (analyticOrderAt_le_of_monic_relation hGd hh d c hmon)
  -- the quotient satisfies a monic relation
  have hE : ∀ z, e z ^ d + ∑ i ∈ range d, (c i).eval z * e z ^ i = 0 := by
    have hprod : Set.EqOn (fun z => h z ^ d *
        (e z ^ d + ∑ i ∈ range d, (c i).eval z * e z ^ i)) 0 Set.univ := by
      intro z _
      have := hmon z
      simp only [G, hGe z] at this
      simp only [Pi.zero_apply]
      rw [← this, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < d := Finset.mem_range.mp hi
        have hexp : d = i + (d - i) := by omega
        conv_lhs => rw [hexp]
        rw [pow_add]
        ring
    have hhd : AnalyticOnNhd ℂ (fun z => h z ^ d) Set.univ :=
      fun z _ => (hh.differentiableOn.analyticAt Filter.univ_mem).pow d
    have hEa : AnalyticOnNhd ℂ
        (fun z => e z ^ d + ∑ i ∈ range d, (c i).eval z * e z ^ i) Set.univ := by
      intro z _
      have hea : AnalyticAt ℂ e z := he.differentiableOn.analyticAt Filter.univ_mem
      refine (hea.pow d).add ?_
      have : (fun z => ∑ i ∈ range d, (c i).eval z * e z ^ i) =
          ∑ i ∈ range d, (fun z => (c i).eval z * e z ^ i) := by
        funext w; simp
      rw [this]
      exact Finset.analyticAt_sum _ fun i _ =>
        ((Polynomial.differentiable _).differentiableOn.analyticAt Filter.univ_mem).mul
          (hea.pow i)
    rcases Bottcher.analyticOnNhd_domain hhd hEa isPreconnected_univ isOpen_univ hprod with
      h1 | h2
    · obtain ⟨z₀, hz₀⟩ := hh0
      exact absurd (pow_eq_zero_iff (by omega) |>.mp (h1 (Set.mem_univ z₀))) hz₀
    · intro z
      exact h2 (Set.mem_univ z)
  -- an entire function algebraic over the coordinate is a polynomial
  obtain ⟨r, hr⟩ : ∃ r : Polynomial ℂ, ∀ z, e z = r.eval z := by
    apply (differentiallyAlgebraicOfOrder_zero_iff_polynomial he).mp
    let Q : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 1 ^ d +
      ∑ i ∈ range d, Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (c i) *
        MvPolynomial.X 1 ^ i
    have hQeval : ∀ z y : ℂ, MvPolynomial.eval ![z, y] Q =
        y ^ d + ∑ i ∈ range d, (c i).eval z * y ^ i := by
      intro z y
      simp only [Q, map_add, map_pow, map_sum, map_mul, MvPolynomial.eval_X]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [Polynomial.hom_eval₂, MvPolynomial.eval_X]
      have hcomp : (MvPolynomial.eval ![z, y]).comp MvPolynomial.C = RingHom.id ℂ := by
        ext a
        simp
      rw [hcomp]
      rfl
    refine ⟨Q, ?_, ?_⟩
    · intro hQ
      let p : Polynomial ℂ := Polynomial.X ^ d +
        ∑ i ∈ range d, Polynomial.C ((c i).eval 0) * Polynomial.X ^ i
      have hpd : p.coeff d = 1 := by
        simp only [p, Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_eq_zero (fun i hi => if_neg (by have := Finset.mem_range.mp hi; omega)),
          add_zero]
        simp
      have hp0 : p = 0 := by
        apply Polynomial.funext
        intro y
        have := congrArg (MvPolynomial.eval ![(0 : ℂ), y]) hQ
        rw [hQeval, map_zero] at this
        simp [p, Polynomial.eval_finsetSum, this]
      rw [hp0, Polynomial.coeff_zero] at hpd
      exact zero_ne_one hpd
    · intro z
      have hcons : (Fin.cons z fun j : Fin 1 => iteratedDeriv (j : ℕ) e z : Fin 2 → ℂ) =
          ![z, e z] := by
        funext j
        fin_cases j <;> simp
      rw [hcons, hQeval]
      exact hE z
  exact ⟨r, fun z => by rw [show q.leadingCoeff.eval z * g z = G z from rfl, hGe z, hr z]⟩

end

end GaloisForLFunctions.HTGeometry
