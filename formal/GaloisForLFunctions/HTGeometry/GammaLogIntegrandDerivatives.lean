import GaloisForLFunctions.HTGeometry.GammaLogIntegrand

/-!
# Derivatives of the log-coordinate Gamma integrand

Differentiating `e^{(σ+k)u − e^u}` produces `(σ+k)` times itself minus the same expression with `k`
raised by one, so finite combinations of these shifted integrands are closed under differentiation.
Each of them is integrable for positive `σ`, so *every* iterated derivative of the log-coordinate
Gamma integrand is integrable — the hypothesis under which the Fourier transform of a function decays
faster than any polynomial.
-/

open MeasureTheory Filter Set

namespace GaloisForLFunctions

/-- The shifted log-coordinate integrand. -/
noncomputable def expShift (σ : ℝ) (k : ℕ) (u : ℝ) : ℝ := Real.exp ((σ + k) * u - Real.exp u)

theorem hasDerivAt_expShift (σ : ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (expShift σ k) ((σ + k) * expShift σ k u - expShift σ (k + 1) u) u := by
  have h1 : HasDerivAt (fun u : ℝ => (σ + (k : ℝ)) * u) (σ + k) u := by
    simpa using (hasDerivAt_id u).const_mul (σ + (k : ℝ))
  have hinner : HasDerivAt (fun u : ℝ => (σ + (k : ℝ)) * u - Real.exp u)
      ((σ + k) - Real.exp u) u := h1.sub (Real.hasDerivAt_exp u)
  have h := hinner.exp
  refine h.congr_deriv ?_
  rw [expShift, expShift]
  have hstep : Real.exp ((σ + (k + 1 : ℕ)) * u - Real.exp u)
      = Real.exp u * Real.exp ((σ + k) * u - Real.exp u) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hstep]
  ring

/-- Finite combinations of shifted log-coordinate integrands. -/
def IsExpFamily (σ : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ (K : ℕ) (c : ℕ → ℝ), ∀ u, g u = ∑ k ∈ Finset.range K, c k * expShift σ k u

theorem isExpFamily_base (σ : ℝ) : IsExpFamily σ (expShift σ 0) :=
  ⟨1, fun _ => 1, by intro u; simp⟩

theorem IsExpFamily.integrable {σ : ℝ} (hσ : 0 < σ) {g : ℝ → ℝ} (h : IsExpFamily σ g) :
    Integrable g := by
  obtain ⟨K, c, hg⟩ := h
  have hsum : Integrable (fun u : ℝ => ∑ k ∈ Finset.range K, c k * expShift σ k u) := by
    refine integrable_finsetSum _ fun k _ => ?_
    refine Integrable.const_mul ?_ _
    have hpos : 0 < σ + k := by positivity
    exact integrable_expSubExp hpos
  refine hsum.congr ?_
  filter_upwards with u
  exact (hg u).symm

theorem hasDerivAt_expFamilySum (σ : ℝ) (K : ℕ) (c : ℕ → ℝ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => ∑ k ∈ Finset.range K, c k * expShift σ k u)
      (∑ k ∈ Finset.range K, c k * ((σ + k) * expShift σ k u - expShift σ (k + 1) u)) u := by
  have hterm : ∀ k ∈ Finset.range K, HasDerivAt (fun u : ℝ => c k * expShift σ k u)
      (c k * ((σ + k) * expShift σ k u - expShift σ (k + 1) u)) u :=
    fun k _ => ((hasDerivAt_expShift σ k u).const_mul (c k))
  have h := HasDerivAt.sum hterm
  have hfun : (∑ i ∈ Finset.range K, fun u : ℝ => c i * expShift σ i u)
      = fun u : ℝ => ∑ k ∈ Finset.range K, c k * expShift σ k u := by
    funext u
    simp [Finset.sum_apply]
  rwa [hfun] at h

theorem IsExpFamily.deriv {σ : ℝ} {g : ℝ → ℝ} (h : IsExpFamily σ g) :
    IsExpFamily σ (_root_.deriv g) := by
  classical
  obtain ⟨K, c, hg⟩ := h
  refine ⟨K + 1, fun k => (if k < K then c k * (σ + k) else 0)
    - (if k = 0 then 0 else if k - 1 < K then c (k - 1) else 0), fun u => ?_⟩
  have hfun : g = fun u => ∑ k ∈ Finset.range K, c k * expShift σ k u := funext hg
  have hderiv : _root_.deriv g u
      = ∑ k ∈ Finset.range K, c k * ((σ + k) * expShift σ k u - expShift σ (k + 1) u) := by
    rw [hfun]
    exact (hasDerivAt_expFamilySum σ K c u).deriv
  rw [hderiv]
  have hleft : ∑ k ∈ Finset.range (K + 1), (if k < K then c k * (σ + k) else 0) * expShift σ k u
      = ∑ k ∈ Finset.range K, (c k * (σ + k)) * expShift σ k u := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl K), zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_range.mp hk)]
  have hright : ∑ k ∈ Finset.range (K + 1),
      (if k = 0 then 0 else if k - 1 < K then c (k - 1) else 0) * expShift σ k u
      = ∑ k ∈ Finset.range K, c k * expShift σ (k + 1) u := by
    rw [Finset.sum_range_succ']
    have hzero : (if (0 : ℕ) = 0 then (0 : ℝ) else if 0 - 1 < K then c (0 - 1) else 0) = 0 := by
      simp
    rw [hzero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < K := Finset.mem_range.mp hk
    rw [if_neg (Nat.succ_ne_zero k)]
    simp only [Nat.add_sub_cancel]
    rw [if_pos hk']
  have hL : ∑ k ∈ Finset.range K, c k * ((σ + k) * expShift σ k u - expShift σ (k + 1) u)
      = (∑ k ∈ Finset.range K, (c k * (σ + k)) * expShift σ k u)
        - ∑ k ∈ Finset.range K, c k * expShift σ (k + 1) u := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hL, ← hleft, ← hright, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem isExpFamily_iteratedDeriv (σ : ℝ) (n : ℕ) :
    IsExpFamily σ (iteratedDeriv n (expShift σ 0)) := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using isExpFamily_base σ
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- **Every derivative of the log-coordinate Gamma integrand is integrable.** -/
theorem integrable_iteratedDeriv_expShift {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Integrable (iteratedDeriv n (expShift σ 0)) :=
  (isExpFamily_iteratedDeriv σ n).integrable hσ

/-- The log-coordinate Gamma integrand is smooth. -/
theorem contDiff_expShift (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (expShift σ 0) := by
  have hfun : expShift σ 0 = fun u : ℝ => Real.exp ((σ + (0 : ℕ)) * u - Real.exp u) := rfl
  rw [hfun]
  fun_prop

end GaloisForLFunctions
