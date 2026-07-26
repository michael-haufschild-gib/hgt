import GaloisForLFunctions.HTGeometry.EllipticJetValueMap

/-!
# Periodicity and regularity of the differential monomials

Bookkeeping for the elliptic counting argument: the monomials `fⁱ (f')ʲ` and their finite
combinations inherit the periodicity of `f`, are analytic wherever `f` is, and are meromorphic
wherever `f` is.

* `periodic_diffMonomial`, `periodic_monomialCombination`;
* `analyticAt_diffMonomial`, `analyticAt_monomialCombination`;
* `meromorphicAt_diffMonomial`, `meromorphicAt_monomialCombination`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Every differential monomial of a periodic function is periodic. -/
theorem periodic_diffMonomial {f : ℂ → ℂ} {p : ℂ} (h : Function.Periodic f p) (i j : ℕ) :
    Function.Periodic (diffMonomial f i j) p := by
  intro z
  show f (z + p) ^ i * deriv f (z + p) ^ j = f z ^ i * deriv f z ^ j
  rw [h z, periodic_deriv h z]

/-- A finite combination of the differential monomials of a periodic function is periodic. -/
theorem periodic_monomialCombination {f : ℂ → ℂ} {p : ℂ} (h : Function.Periodic f p) {N : ℕ}
    (c : (Fin (N + 1) × Fin (N + 1)) → ℂ) :
    Function.Periodic
      (fun z => ∑ q : Fin (N + 1) × Fin (N + 1), c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) z) p := by
  intro z
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [periodic_diffMonomial h (q.1 : ℕ) (q.2 : ℕ) z]

/-- Where `f` is analytic, so is each of its differential monomials. -/
theorem analyticAt_diffMonomial {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) (i j : ℕ) :
    AnalyticAt ℂ (diffMonomial f i j) z :=
  (h.pow i).mul (h.deriv.pow j)

/-- Where `f` is analytic, so is every finite combination of its differential monomials. -/
theorem analyticAt_monomialCombination {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) {N : ℕ}
    (c : (Fin (N + 1) × Fin (N + 1)) → ℂ) :
    AnalyticAt ℂ
      (fun w => ∑ q : Fin (N + 1) × Fin (N + 1), c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) w) z :=
  analyticAt_finset_sum_apply _ _ _
    (fun q _ => analyticAt_const.mul (analyticAt_diffMonomial h (q.1 : ℕ) (q.2 : ℕ)))

/-- Where `f` is meromorphic, so is each of its differential monomials. -/
theorem meromorphicAt_diffMonomial {f : ℂ → ℂ} {z : ℂ} (h : MeromorphicAt f z) (i j : ℕ) :
    MeromorphicAt (diffMonomial f i j) z :=
  (h.pow i).mul (h.deriv.pow j)

/-- Where `f` is meromorphic, so is every finite combination of its differential monomials. -/
theorem meromorphicAt_monomialCombination {f : ℂ → ℂ} {z : ℂ} (h : MeromorphicAt f z) {N : ℕ}
    (c : (Fin (N + 1) × Fin (N + 1)) → ℂ) :
    MeromorphicAt
      (fun w => ∑ q : Fin (N + 1) × Fin (N + 1), c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) w) z := by
  classical
  have hgen : ∀ s : Finset (Fin (N + 1) × Fin (N + 1)),
      MeromorphicAt (fun w => ∑ q ∈ s, c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) w) z := by
    intro s
    induction s using Finset.induction with
    | empty =>
        have hz : (fun w : ℂ => ∑ q ∈ (∅ : Finset (Fin (N + 1) × Fin (N + 1))),
            c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) w) = fun _ => (0 : ℂ) := by
          funext w
          simp
        rw [hz]
        exact analyticAt_const.meromorphicAt
    | insert a t ha ih =>
        have hsplit : (fun w : ℂ => ∑ q ∈ insert a t, c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) w)
            = (fun w : ℂ => c a * diffMonomial f (a.1 : ℕ) (a.2 : ℕ) w)
              + fun w : ℂ => ∑ q ∈ t, c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) w := by
          funext w
          show ∑ q ∈ insert a t, c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) w
            = c a * diffMonomial f (a.1 : ℕ) (a.2 : ℕ) w
              + ∑ q ∈ t, c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) w
          rw [Finset.sum_insert ha]
        rw [hsplit]
        exact (analyticAt_const.meromorphicAt.mul
          (meromorphicAt_diffMonomial h (a.1 : ℕ) (a.2 : ℕ))).add ih
  exact hgen Finset.univ

end GaloisForLFunctions.HTGeometry
