import GaloisForLFunctions.HTGeometry.EllipticJetVanishing

/-!
# From a monomial relation to an algebraic differential equation

The counting argument ends with a nonzero coefficient vector `c` such that the combination
`∑ c_q fⁱ (f')ʲ` vanishes off the poles.  At a pole the normal form gives `f = 0` and `deriv f = 0`,
so multiplying the relation by the value slot makes it hold *everywhere*:

`(∑ c_q f(z)ⁱ f'(z)ʲ) · f(z) = 0` for all `z`.

That is already an algebraic differential equation of order one.  Its differential polynomial is
`(∑ c_q y₀ⁱ y₁ʲ) · y₀`, nonzero because the monomials `y₀ⁱ y₁ʲ` are distinct — the coefficient of the
monomial attached to any index with `c_q ≠ 0` is `c_q` — and because `MvPolynomial` over a field is a
domain.  The same device appears in `weierstrassPRelation`, where multiplying by the value slot
repairs the junk values of `℘` at the lattice.

* **`differentiallyAlgebraic_of_monomial_relation`**.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- The exponent vector of the monomial `y₀ⁱ y₁ʲ` in the jet variables. -/
private noncomputable def jetKey (i j : ℕ) : Fin 3 →₀ ℕ := Finsupp.single 1 i + Finsupp.single 2 j

private theorem jetKey_apply_one (i j : ℕ) : jetKey i j 1 = i := by
  simp [jetKey, Finsupp.add_apply]

private theorem jetKey_apply_two (i j : ℕ) : jetKey i j 2 = j := by
  simp [jetKey, Finsupp.add_apply]

private theorem jetKey_apply_zero (i j : ℕ) : jetKey i j 0 = 0 := by
  simp [jetKey, Finsupp.add_apply]

private theorem jetKey_injective {i j i' j' : ℕ} (h : jetKey i j = jetKey i' j') :
    i = i' ∧ j = j' := by
  constructor
  · have := congrArg (fun s : Fin 3 →₀ ℕ => s 1) h
    simpa [jetKey_apply_one] using this
  · have := congrArg (fun s : Fin 3 →₀ ℕ => s 2) h
    simpa [jetKey_apply_two] using this

private theorem eval_monomial_jetKey (v : Fin 3 → ℂ) (i j : ℕ) (a : ℂ) :
    MvPolynomial.eval v (MvPolynomial.monomial (jetKey i j) a) = a * (v 1 ^ i * v 2 ^ j) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun k => pow_zero (v k)),
    Fin.prod_univ_three, jetKey_apply_zero, jetKey_apply_one, jetKey_apply_two]
  ring

/-- **A monomial relation is an algebraic differential equation.**  If a nonzero coefficient vector
makes `(∑ c_q fⁱ (f')ʲ) · f` vanish identically, then `f` is differentially algebraic. -/
theorem differentiallyAlgebraic_of_monomial_relation {f : ℂ → ℂ} {N : ℕ}
    (c : (Fin (N + 1) × Fin (N + 1)) → ℂ) (hc : c ≠ 0)
    (hrel : ∀ z, (∑ q : Fin (N + 1) × Fin (N + 1),
        c q * (f z ^ (q.1 : ℕ) * deriv f z ^ (q.2 : ℕ))) * f z = 0) :
    DifferentiallyAlgebraic f := by
  classical
  set A : MvPolynomial (Fin 3) ℂ :=
    ∑ q : Fin (N + 1) × Fin (N + 1),
      MvPolynomial.monomial (jetKey (q.1 : ℕ) (q.2 : ℕ)) (c q) with hA
  -- the coefficient of the monomial attached to an index recovers the coefficient
  have hcoeff : ∀ q₀ : Fin (N + 1) × Fin (N + 1),
      MvPolynomial.coeff (jetKey (q₀.1 : ℕ) (q₀.2 : ℕ)) A = c q₀ := by
    intro q₀
    have hsingle : (∑ q : Fin (N + 1) × Fin (N + 1),
        MvPolynomial.coeff (jetKey (q₀.1 : ℕ) (q₀.2 : ℕ))
          (MvPolynomial.monomial (jetKey (q.1 : ℕ) (q.2 : ℕ)) (c q)))
        = MvPolynomial.coeff (jetKey (q₀.1 : ℕ) (q₀.2 : ℕ))
          (MvPolynomial.monomial (jetKey (q₀.1 : ℕ) (q₀.2 : ℕ)) (c q₀)) := by
      refine Finset.sum_eq_single_of_mem q₀ (Finset.mem_univ q₀) (fun q _ hne => ?_)
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hkey
      obtain ⟨h1, h2⟩ := jetKey_injective hkey
      exact hne (Prod.ext (Fin.ext h1) (Fin.ext h2))
    rw [hA, MvPolynomial.coeff_sum, hsingle, MvPolynomial.coeff_monomial, if_pos rfl]
  have hAne : A ≠ 0 := by
    intro h0
    obtain ⟨q₀, hq₀⟩ : ∃ q₀, c q₀ ≠ 0 := by
      by_contra hall
      exact hc (funext fun q => not_not.mp (fun h => hall ⟨q, h⟩))
    exact hq₀ (by rw [← hcoeff q₀, h0, MvPolynomial.coeff_zero])
  refine ⟨1, A * MvPolynomial.X 1, mul_ne_zero hAne (MvPolynomial.X_ne_zero 1), fun z => ?_⟩
  set v : Fin 3 → ℂ := Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) with hv
  have hv1 : v 1 = f z := by
    rw [hv, show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
    simp [iteratedDeriv_zero]
  have hv2 : v 2 = deriv f z := by
    rw [hv, show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]
    simp [iteratedDeriv_one]
  have hevalA : MvPolynomial.eval v A
      = ∑ q : Fin (N + 1) × Fin (N + 1), c q * (f z ^ (q.1 : ℕ) * deriv f z ^ (q.2 : ℕ)) := by
    rw [hA, map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [eval_monomial_jetKey, hv1, hv2]
  rw [map_mul, hevalA, MvPolynomial.eval_X, hv1]
  exact hrel z

end GaloisForLFunctions.HTGeometry
