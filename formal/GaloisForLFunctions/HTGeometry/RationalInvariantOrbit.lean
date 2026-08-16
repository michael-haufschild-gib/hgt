import GaloisForLFunctions.HTGeometry.RationalOrderComposition

/-!
# Invariant differentials transport their orders along orbits

An invariance relation `Q ∘ R · (R')^k = λ Q` for a nonconstant polynomial `R` reads on orders at a
point `a` as

`ord_{R(a)}(Q) · e_a + k · m_a = ord_a(Q)`,

where `e_a` is the multiplicity of `a` as a root of `R − R(a)` and `m_a` the multiplicity of `a` as
a root of `R'`.  Away from the critical points both corrections are trivial — `e_a = 1`, `m_a = 0` —
so the order is constant along the whole forward orbit.

A nonzero rational function has only finitely many zeros and poles, so an injective critical-free
orbit forces the common order to vanish.  This is the mechanism that kills invariant differentials
for a map whose critical orbit is infinite.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A simple root is one where the derivative survives. -/
theorem rootMultiplicity_eq_one {p : K[X]} (hp : p ≠ 0) {a : K} (h0 : p.eval a = 0)
    (h1 : (derivative p).eval a ≠ 0) : rootMultiplicity a p = 1 := by
  have hpos : 0 < rootMultiplicity a p := (rootMultiplicity_pos hp).mpr h0
  have hd := Polynomial.derivative_rootMultiplicity_of_root (p := p) (t := a) h0
  by_contra hne
  have h2 : 2 ≤ rootMultiplicity a p := by omega
  have hdpos : 0 < rootMultiplicity a (derivative p) := by omega
  refine h1 ((rootMultiplicity_pos ?_).mp hdpos)
  intro hz
  rw [hz] at hd
  simp only [rootMultiplicity_zero] at hd
  omega

/-- **Order transport.**  The invariance relation of a rational `k`-differential reads on orders as
a transport law along the map. -/
theorem ratOrder_relation_transport {R : K[X]} (hRdeg : R.natDegree ≠ 0)
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {Q : RatFunc K} (hQ : Q ≠ 0) {k : ℤ} {μ : K} (hμ : μ ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k = RatFunc.C μ * Q) (a : K) :
    ratOrder Q (R.eval a) * (rootMultiplicity a (R - Polynomial.C (R.eval a)) : ℤ)
      + k * (rootMultiplicity a (derivative R) : ℤ) = ratOrder Q a := by
  have hd0 : derivative R ≠ 0 := by
    intro h
    exact hRdeg (Polynomial.derivative_eq_zero.mp h)
  have hAd : algebraMap K[X] (RatFunc K) (derivative R) ≠ 0 :=
    fun h => hd0 ((RatFunc.algebraMap_injective K) (by rw [h, map_zero]))
  have hsub0 : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q ≠ 0 := by
    intro h
    refine hQ ?_
    have hinj := (ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR).injective
      (a₁ := Q) (a₂ := 0)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_zero] at hinj
    exact hinj h
  have hCμ : (RatFunc.C μ : RatFunc K) ≠ 0 := by
    rw [← RatFunc.algebraMap_C]
    intro h
    have hz : (Polynomial.C μ : K[X]) = 0 := (RatFunc.algebraMap_injective K) (by rw [h, map_zero])
    exact hμ (by simpa using hz)
  have h : ratOrder (ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q
      * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k) a
      = ratOrder (RatFunc.C μ * Q) a := by rw [hrel]
  rw [ratOrder_mul hsub0 (zpow_ne_zero k hAd), ratOrder_zpow hAd, ratOrder_algebraMap,
    ratOrder_ratFuncSubstitution hRdeg hR hQ, ratOrder_mul hCμ hQ, ratOrder_C] at h
  omega

/-- **Away from the critical points the order is constant along the map.** -/
theorem ratOrder_eval_eq_of_deriv_ne_zero {R : K[X]} (hRdeg : R.natDegree ≠ 0)
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {Q : RatFunc K} (hQ : Q ≠ 0) {k : ℤ} {μ : K} (hμ : μ ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k = RatFunc.C μ * Q)
    {a : K} (ha : (derivative R).eval a ≠ 0) :
    ratOrder Q (R.eval a) = ratOrder Q a := by
  have hRb : R - Polynomial.C (R.eval a) ≠ 0 := by
    intro h
    exact hRdeg (by rw [sub_eq_zero.mp h, natDegree_C])
  have hval : (R - Polynomial.C (R.eval a)).eval a = 0 := by
    rw [eval_sub, eval_C, sub_self]
  have hder : derivative (R - Polynomial.C (R.eval a)) = derivative R := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero]
  have hmult : rootMultiplicity a (R - Polynomial.C (R.eval a)) = 1 :=
    rootMultiplicity_eq_one hRb hval (by rw [hder]; exact ha)
  have hzero : rootMultiplicity a (derivative R) = 0 := rootMultiplicity_eq_zero ha
  have h := ratOrder_relation_transport hRdeg hR hQ hμ hrel a
  rw [hmult, hzero] at h
  simpa using h

/-- **An injective critical-free orbit forces the order to vanish.** -/
theorem ratOrder_eq_zero_of_orbit {R : K[X]} (hRdeg : R.natDegree ≠ 0)
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {Q : RatFunc K} (hQ : Q ≠ 0) {k : ℤ} {μ : K} (hμ : μ ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k = RatFunc.C μ * Q)
    {f : ℕ → K} (hstep : ∀ n, f (n + 1) = R.eval (f n))
    (hcrit : ∀ n, (derivative R).eval (f n) ≠ 0) (hinj : Function.Injective f) :
    ratOrder Q (f 0) = 0 := by
  have hconst : ∀ n, ratOrder Q (f n) = ratOrder Q (f 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [hstep n, ratOrder_eval_eq_of_deriv_ne_zero hRdeg hR hQ hμ hrel (hcrit n), ih]
  by_contra hne
  have hsub : Set.range f ⊆ {c : K | ratOrder Q c ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    show ratOrder Q (f n) ≠ 0
    rw [hconst n]
    exact hne
  exact (Set.infinite_range_of_injective hinj) ((finite_support_ratOrder hQ).subset hsub)

end

end GaloisForLFunctions.HTGeometry
