import GaloisForLFunctions.HTGeometry.StdRatLineRigidity
import GaloisForLFunctions.HTGeometry.PolygammaDepthExpansion
import GaloisForLFunctions.HTGeometry.VerticalFlatGermElimination
import GaloisForLFunctions.HTGeometry.JetPolyCoeffDatum

/-!
# Every nonzero jet polynomial has a datum on every line

Hölder's theorem in germ form says no nonzero differential polynomial in the digamma jets is flat on
a half-plane.  Standard rational approximations of every depth transfer decay from one vertical line
to all of them, so "flat on one line" already means "flat on the half-plane".

Together: a nonzero polynomial in the positive-order digamma jets fails to have arbitrarily high
decay order on any single line, and the residue machinery then produces its datum — a pair `(p, c)`
with `c ≠ 0` and `s^p·A(s) → c` along the line.  This is the existential half of the finite phase
law's coefficient hypothesis, with no presentation supplied.
-/

open Filter Topology Complex MvPolynomial

namespace GaloisForLFunctions

/-- A jet polynomial with complex constant coefficients, as a polynomial in the jet variables over
the field of rational functions. -/
noncomputable def jetPolyMv (N M : ℕ) (a : Fin M → ℂ) (e : Fin M → Fin N → ℕ) :
    MvPolynomial (Fin (N + 1)) (RatFunc ℂ) :=
  ∑ α : Fin M, MvPolynomial.C (algebraMap ℂ (RatFunc ℂ) (a α))
    * ∏ i : Fin N, (MvPolynomial.X i.succ) ^ e α i

/-- A product of monomials is the monomial of the sum of exponent vectors. -/
theorem prod_monomial_one {ι τ R : Type*} [CommSemiring R] (s : Finset ι) (f : ι → (τ →₀ ℕ)) :
    ∏ i ∈ s, (MvPolynomial.monomial (f i) (1 : R)) = MvPolynomial.monomial (∑ i ∈ s, f i) 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPolynomial.monomial_mul, one_mul]

/-- The exponent vector of a jet monomial. -/
noncomputable def jetExp {N : ℕ} (e : Fin N → ℕ) : Fin (N + 1) →₀ ℕ :=
  ∑ i : Fin N, Finsupp.single i.succ (e i)

theorem jetExp_apply_succ {N : ℕ} (e : Fin N → ℕ) (j : Fin N) : jetExp e j.succ = e j := by
  classical
  rw [jetExp, Finset.sum_apply']
  rw [Finset.sum_eq_single j]
  · rw [Finsupp.single_eq_same]
  · intro i _ hij
    exact Finsupp.single_eq_of_ne (fun h => hij (Fin.succ_injective _ h).symm)
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem jetExp_injective {N : ℕ} : Function.Injective (jetExp (N := N)) := by
  intro e f hef
  funext j
  rw [← jetExp_apply_succ e j, ← jetExp_apply_succ f j, hef]

/-- The jet monomial in the polynomial ring is the monomial of its exponent vector. -/
theorem prod_X_succ_pow {N : ℕ} (e : Fin N → ℕ) :
    (∏ i : Fin N, (MvPolynomial.X i.succ : MvPolynomial (Fin (N + 1)) (RatFunc ℂ)) ^ e i)
      = MvPolynomial.monomial (jetExp e) 1 := by
  rw [Finset.prod_congr rfl fun i _ =>
    MvPolynomial.X_pow_eq_monomial (R := RatFunc ℂ) (n := i.succ) (e := e i)]
  rw [prod_monomial_one, jetExp]

/-- **A jet polynomial with a nonzero coefficient is nonzero.** -/
theorem jetPolyMv_ne_zero {N M : ℕ} (a : Fin M → ℂ) (e : Fin M → Fin N → ℕ)
    (he : Function.Injective e) {β : Fin M} (hβ : a β ≠ 0) : jetPolyMv N M a e ≠ 0 := by
  classical
  intro h0
  have hcoeff : MvPolynomial.coeff (jetExp (e β)) (jetPolyMv N M a e)
      = algebraMap ℂ (RatFunc ℂ) (a β) := by
    rw [jetPolyMv, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single β]
    · rw [prod_X_succ_pow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, if_pos rfl,
        mul_one]
    · intro α _ hαβ
      rw [prod_X_succ_pow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
        if_neg (fun h => hαβ (he (jetExp_injective h))), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ β) h
  rw [h0, MvPolynomial.coeff_zero] at hcoeff
  exact hβ ((map_eq_zero_iff _ (algebraMap ℂ (RatFunc ℂ)).injective).mp hcoeff.symm)

/-- The evaluation of a jet polynomial at the digamma jets is the germ of the corresponding function
on the line. -/
theorem digammaJetEval_jetPolyMv (σ₀ : ℝ) (N M : ℕ) (a : Fin M → ℂ) (e : Fin M → Fin N → ℕ) :
    digammaJetEval σ₀ (N + 1) (jetPolyMv N M a e)
      = ((fun s : ℂ => ∑ α : Fin M, a α * ∏ i : Fin N,
          iteratedDeriv ((i : ℕ) + 1) Complex.digamma s ^ e α i : ℂ → ℂ) : HalfPlaneGerm σ₀) := by
  classical
  set Φ : (ℂ → ℂ) →+* HalfPlaneGerm σ₀ := Filter.Germ.coeRingHom (halfPlaneUpper σ₀) with hΦ
  have hgoal : ((fun s : ℂ => ∑ α : Fin M, a α * ∏ i : Fin N,
      iteratedDeriv ((i : ℕ) + 1) Complex.digamma s ^ e α i : ℂ → ℂ) : HalfPlaneGerm σ₀)
      = ∑ α : Fin M, Φ (fun _ : ℂ => a α)
          * ∏ i : Fin N, Φ (fun s : ℂ => iteratedDeriv ((i : ℕ) + 1) Complex.digamma s) ^ e α i := by
    have hpush : ∑ α : Fin M, Φ (fun _ : ℂ => a α)
        * ∏ i : Fin N, Φ (fun s : ℂ => iteratedDeriv ((i : ℕ) + 1) Complex.digamma s) ^ e α i
        = Φ (∑ α : Fin M, (fun _ : ℂ => a α)
            * ∏ i : Fin N, (fun s : ℂ => iteratedDeriv ((i : ℕ) + 1) Complex.digamma s) ^ e α i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_mul, map_prod]
      simp only [map_pow]
    rw [hpush]
    congr 1
    funext s
    simp [Finset.sum_apply, Finset.prod_apply]
  rw [hgoal, jetPolyMv, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_prod]
  congr 1
  · rw [digammaJetEval_C,
      show algebraMap ℂ (RatFunc ℂ) (a α)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (a α)) by simp,
      ratGerm_algebraMap]
    simp [polyGerm, hΦ, Filter.Germ.coeRingHom]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, digammaJetEval_X, digammaJetGerm, Fin.val_succ]
    rfl

/-- **A nonzero jet polynomial has bounded decay order on every line.**  Flatness on a single line
would be flatness on the half-plane, which Hölder's theorem forbids. -/
theorem exists_not_isLineBigO_jetPoly {σ : ℝ} (hσ : 0 < σ) (N M W : ℕ) (a : Fin M → ℂ)
    (e : Fin M → Fin N → ℕ) (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i)
    (hne : jetPolyMv N M a e ≠ 0) :
    ∃ n : ℕ, ¬ IsLineBigO σ n (fun t : ℝ => ∑ α : Fin M, a α * ∏ i : Fin N,
      iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i) := by
  by_contra hcon
  push Not at hcon
  set g : ℂ → ℂ := fun s : ℂ => ∑ α : Fin M, a α * ∏ i : Fin N,
    iteratedDeriv ((i : ℕ) + 1) Complex.digamma s ^ e α i with hg
  have hpkg : ∀ K : ℕ, ∃ (F : ℂ → ℂ) (A : ℝ), IsStdRat F W ∧ 0 ≤ A ∧
      ∀ σ' t : ℝ, 0 < σ' → 2 ≤ t →
        ‖g ((σ' : ℂ) + (t : ℂ) * Complex.I) - F ((σ' : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ A * (1 / t) ^ (W + K) := by
    intro K
    obtain ⟨F, A, hstd, hA, hb⟩ := exists_jetPoly_package N M K W e a hW
    exact ⟨F, A, hstd, le_trans zero_le_one hA, hb⟩
  have hflat : IsVertFlat σ g := isVertFlat_of_isLineBigO_all hσ hpkg hcon hσ
  refine not_isVertFlatGerm_digammaJetEval (σ₀ := σ) hσ.le (m := N + 1) hne ?_
  rw [digammaJetEval_jetPolyMv]
  exact hflat

/-- **The datum of a nonzero jet polynomial.**  No presentation is supplied: nonvanishing alone
produces the residue `s^p·A(s) → c ≠ 0` along the line. -/
theorem exists_jetPoly_datum_of_ne_zero {σ : ℝ} (hσ : 0 < σ) (N M W : ℕ) (a : Fin M → ℂ)
    (e : Fin M → Fin N → ℕ) (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i)
    (hne : jetPolyMv N M a e ≠ 0) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ Tendsto (fun t : ℝ =>
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * (∑ α : Fin M, a α * ∏ i : Fin N,
        iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i))
      atTop (nhds c) := by
  obtain ⟨n, hn⟩ := exists_not_isLineBigO_jetPoly hσ N M W a e hW hne
  have hfun : (fun t : ℝ => ∑ α : Fin M,
      ((Polynomial.C (a α)).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (0 : ℕ))
        * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
      = (fun t : ℝ => ∑ α : Fin M, a α * ∏ i : Fin N,
        iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i) := by
    funext t
    refine Finset.sum_congr rfl fun α _ => ?_
    simp
  obtain ⟨p, c, hc, hlim⟩ :=
    exists_jetPolyCoeff_datum hσ N M W 0 e (fun α => Polynomial.C (a α))
      (fun α => by simp) hW (n := n) (by rw [hfun]; exact hn)
  refine ⟨p, c, hc, hlim.congr fun t => ?_⟩
  congr 1
  exact congrFun hfun t

end GaloisForLFunctions
