import GaloisForLFunctions.HTGeometry.AutonomousFirstOrderEntireClassification
import GaloisForLFunctions.HTGeometry.LaurentExpGrowth
import GaloisForLFunctions.HTGeometry.EntireCascadeLaurentTower
import GaloisForLFunctions.HTGeometry.FiniteOrderCascadeCompositionDepth

/-!
# Unit differential-order cost for autonomous first-order entire cascades

For transcendental entire `f₁, …, f_n`, each satisfying a nonzero autonomous first-order algebraic
differential equation `P_k(f_k, f_k') = 0`, the composition `F_n = f_n ∘ ⋯ ∘ f₁` has

* minimal algebraic differential order exactly `n`, and
* exact positive-lower-order composition depth `n`.

In particular `ord_DA(f^[n]) = cd₊(f^[n]) = n` for every transcendental entire solution `f` of an
autonomous first-order algebraic differential equation.

The exact order is the corpus's universal first-order cascade theorem.  The composition depth needs
finite order and positive lower order of every factor; both follow from the entire Briot–Bouquet
classification `f(z) = p(e^{az}) / e^{maz}` proved in `AutonomousFirstOrderEntireClassification`.
-/

open Filter Topology Metric Set Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

/-! ## From a bivariate relation to a first-order differential equation -/

/-- A bivariate polynomial vanishing everywhere is zero. -/
theorem eq_zero_of_relEval_eq_zero {Q : Polynomial (Polynomial ℂ)}
    (h : ∀ a b : ℂ, relEval Q a b = 0) : Q = 0 := by
  ext j : 1
  rw [Polynomial.coeff_zero]
  apply Polynomial.funext
  intro a
  have hmap : Q.map (evalRingHom a) = 0 := Polynomial.funext fun b => by
    simpa [relEval] using h a b
  have := congrArg (fun q => q.coeff j) hmap
  simpa [coeff_map] using this

/-- The first-order differential polynomial `Q(X₁, X₂)` in the variables `(z, f, f')`. -/
noncomputable def relMv (Q : Polynomial (Polynomial ℂ)) : MvPolynomial (Fin 3) ℂ :=
  Q.eval₂ (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 1)) (MvPolynomial.X 2)

theorem eval_relMv (Q : Polynomial (Polynomial ℂ)) (v : Fin 3 → ℂ) :
    MvPolynomial.eval v (relMv Q) = relEval Q (v 1) (v 2) := by
  rw [relMv, Polynomial.hom_eval₂, relEval, eval_map, MvPolynomial.eval_X]
  congr 1
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp
  · simp

/-- **A nonzero autonomous first-order relation is a first-order algebraic differential
equation.** -/
theorem differentiallyAlgebraicOfOrder_one_of_relEval {f : ℂ → ℂ} {Q : Polynomial (Polynomial ℂ)}
    (hQ : Q ≠ 0) (hrel : ∀ z, relEval Q (f z) (deriv f z) = 0) :
    DifferentiallyAlgebraicOfOrder f 1 := by
  refine ⟨relMv Q, fun h0 => hQ (eq_zero_of_relEval_eq_zero fun a b => ?_), fun z => ?_⟩
  · have := congrArg (MvPolynomial.eval (![0, a, b] : Fin 3 → ℂ)) h0
    rw [eval_relMv, map_zero] at this
    simpa using this
  · rw [eval_relMv]
    change relEval Q (iteratedDeriv 0 f z) (iteratedDeriv 1 f z) = 0
    rw [iteratedDeriv_zero, iteratedDeriv_one]
    exact hrel z

/-! ## Growth of autonomous first-order solutions -/

/-- The entire Briot–Bouquet normal form, as an equality of functions. -/
theorem exists_eq_laurentExp_of_autonomous_firstOrder {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0) (hrel : ∀ z, relEval P (f z) (deriv f z) = 0) :
    ∃ (a : ℂ) (p : Polynomial ℂ) (m : ℕ), a ≠ 0 ∧ f = laurentExp a p m := by
  obtain ⟨a, p, m, ha, h⟩ := exists_laurentExp_of_autonomous_firstOrder hf hP hrel
  exact ⟨a, p, m, ha, funext h⟩

/-- **Order at most one.** -/
theorem finiteOrderEnvelope_of_autonomous_firstOrder {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0) (hrel : ∀ z, relEval P (f z) (deriv f z) = 0) :
    FiniteOrderEnvelope f := by
  obtain ⟨a, p, m, -, rfl⟩ := exists_eq_laurentExp_of_autonomous_firstOrder hf hP hrel
  exact finiteOrderEnvelope_laurentExp a p m

/-- **Positive lower order.** -/
theorem positiveLowerOrder_of_autonomous_firstOrder {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0) (hrel : ∀ z, relEval P (f z) (deriv f z) = 0) :
    PositiveLowerOrder f := by
  obtain ⟨a, p, m, ha, rfl⟩ := exists_eq_laurentExp_of_autonomous_firstOrder hf hP hrel
  exact positiveLowerOrder_laurentExp ha (exists_ne_of_transcendentalEntire hf)

/-- **Order and lower order exactly one.**  The maximum modulus of a transcendental entire solution
of an autonomous first-order equation is eventually below `exp(r^δ)` for every `δ > 1` and
eventually above `exp(r^δ)` for every `δ < 1`. -/
theorem order_eq_one_of_autonomous_firstOrder {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0) (hrel : ∀ z, relEval P (f z) (deriv f z) = 0) :
    (∀ δ : ℝ, 1 < δ → ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ Real.exp (r ^ δ)) ∧
      (∀ δ : ℝ, δ < 1 → ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ ≤ r ∧ Real.exp (r ^ δ) ≤ ‖f z‖) := by
  obtain ⟨a, p, m, ha, rfl⟩ := exists_eq_laurentExp_of_autonomous_firstOrder hf hP hrel
  exact ⟨fun δ hδ => eventually_norm_laurentExp_le_exp_rpow a p m hδ,
    fun δ hδ => eventually_exp_rpow_le_norm_laurentExp ha (exists_ne_of_transcendentalEntire hf) hδ⟩

/-! ## The unit-cost law -/

/-- **Unit differential-order cost and exact composition depth for autonomous first-order entire
cascades.** -/
theorem exactOrder_and_compositionDepth_autonomousFirstOrderCascade {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ k, k < n → TranscendentalEntire (f k))
    (hrel : ∀ k, k < n → ∃ P : Polynomial (Polynomial ℂ), P ≠ 0 ∧
      ∀ z, relEval P (f k z) (deriv (f k) z) = 0) :
    ExactDifferentialOrder (entireCascade f n) n ∧
      CompositionDepthAtLeast (entireCascade f n) n ∧
      ¬ CompositionDepthAtLeast (entireCascade f n) (n + 1) := by
  have h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1 := fun k hk => by
    obtain ⟨P, hP, hPrel⟩ := hrel k hk
    exact differentiallyAlgebraicOfOrder_one_of_relEval hP hPrel
  refine ⟨exactDifferentialOrder_entireCascade_of_lt hall h1, ?_⟩
  exact compositionDepth_finiteOrder_positiveCascade n (fun k hk => (hall k hk).1)
    (fun k hk => exists_ne_of_transcendentalEntire (hall k hk))
    (fun k hk => by
      obtain ⟨P, hP, hPrel⟩ := hrel k hk
      exact finiteOrderEnvelope_of_autonomous_firstOrder (hall k hk) hP hPrel)
    (fun k hk => by
      obtain ⟨P, hP, hPrel⟩ := hrel k hk
      exact positiveLowerOrder_of_autonomous_firstOrder (hall k hk) hP hPrel)

theorem entireCascade_const_eq_iterate (f : ℂ → ℂ) (n : ℕ) :
    entireCascade (fun _ => f) n = f^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext z
    rw [entireCascade_succ, ih, Function.iterate_succ_apply']

/-- **`ord_DA(f^[n]) = cd₊(f^[n]) = n`** for every transcendental entire solution of a nonzero
autonomous first-order algebraic differential equation. -/
theorem exactOrder_and_compositionDepth_autonomousFirstOrderIterate {f : ℂ → ℂ}
    (hf : TranscendentalEntire f) {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0)
    (hrel : ∀ z, relEval P (f z) (deriv f z) = 0) (n : ℕ) :
    ExactDifferentialOrder (f^[n]) n ∧ CompositionDepthAtLeast (f^[n]) n ∧
      ¬ CompositionDepthAtLeast (f^[n]) (n + 1) := by
  rw [← entireCascade_const_eq_iterate]
  exact exactOrder_and_compositionDepth_autonomousFirstOrderCascade (fun _ _ => hf)
    (fun _ _ => ⟨P, hP, hrel⟩)

end GaloisForLFunctions.HTGeometry
