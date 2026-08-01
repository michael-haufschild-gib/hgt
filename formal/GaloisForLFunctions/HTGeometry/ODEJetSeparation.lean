import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A finite jet determines a solution of an explicit equation

An explicit scalar equation `y⁽ⁿ⁾ = Φ(y, y', …, y⁽ⁿ⁻¹⁾)` with Lipschitz right-hand side becomes a
first-order system for the jet vector, whose vector field is Lipschitz because each component is
either a coordinate projection or `Φ`.  Uniqueness for Lipschitz ODEs then says two solutions whose
jets agree at a single point have equal jets everywhere, hence are equal.

This is the separation step behind the finite jet embedding of a phase carrier: once the defining
relation has been solved for the top derivative near a regular jet, finitely many observations —
the values of the function and its first `n − 1` derivatives at one time — determine the solution.
-/

open Filter Topology Metric

namespace GaloisForLFunctions

/-- The jet vector of a function up to order `n - 1`. -/
noncomputable def jetVec {n : ℕ} (g : ℝ → ℂ) (t : ℝ) : Fin n → ℂ :=
  fun i => iteratedDeriv (i : ℕ) g t

/-- The companion vector field of an explicit scalar equation of order `n`. -/
noncomputable def companionField {n : ℕ} (Φ : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → (Fin n → ℂ) :=
  fun y i => if h : (i : ℕ) + 1 < n then y ⟨(i : ℕ) + 1, h⟩ else Φ y

theorem lipschitzWith_companionField {n : ℕ} {Φ : (Fin n → ℂ) → ℂ} {K : NNReal}
    (hΦ : LipschitzWith K Φ) : LipschitzWith (max 1 K) (companionField Φ) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have hbase : dist y y' ≤ (max 1 K : ℝ) * dist y y' := by
    have h1 : (1 : ℝ) ≤ (max 1 K : ℝ) := by
      exact_mod_cast le_max_left (1 : NNReal) K
    nlinarith [dist_nonneg (x := y) (y := y')]
  by_cases hi : (i : ℕ) + 1 < n
  · simp only [companionField, dif_pos hi]
    exact le_trans (dist_le_pi_dist y y' _) hbase
  · simp only [companionField, dif_neg hi]
    have hK : dist (Φ y) (Φ y') ≤ (K : ℝ) * dist y y' := hΦ.dist_le_mul y y'
    have hKle : (K : ℝ) ≤ (max 1 K : ℝ) := by
      exact_mod_cast le_max_right (1 : NNReal) K
    calc dist (Φ y) (Φ y') ≤ (K : ℝ) * dist y y' := hK
      _ ≤ (max 1 K : ℝ) * dist y y' := mul_le_mul_of_nonneg_right hKle dist_nonneg

/-- The jet vector of a solution of an explicit scalar equation solves the companion system. -/
theorem hasDerivAt_jetVec {n : ℕ} {Φ : (Fin n → ℂ) → ℂ} {g : ℝ → ℂ} {t : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : iteratedDeriv n g t = Φ (jetVec g t)) :
    HasDerivAt (jetVec (n := n) g) (companionField Φ (jetVec g t)) t := by
  rw [hasDerivAt_pi]
  intro i
  by_cases hi : (i : ℕ) + 1 < n
  · have h := hg (i : ℕ) (by omega) t
    simp only [companionField, dif_pos hi, jetVec]
    exact h
  · have hin : (i : ℕ) + 1 = n := by omega
    have h := hg (i : ℕ) i.2 t
    simp only [companionField, dif_neg hi, jetVec]
    have hval : iteratedDeriv ((i : ℕ) + 1) g t = Φ (jetVec g t) := by
      rw [hin]
      exact hgODE
    rw [← hval]
    exact h

/-- **A finite jet determines a solution of an explicit equation.** -/
theorem jetVec_eq_of_eq_at {n : ℕ} {Φ : (Fin n → ℂ) → ℂ} {K : NNReal} (hΦ : LipschitzWith K Φ)
    {g h : ℝ → ℂ} {t₀ : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : ∀ t, iteratedDeriv n g t = Φ (jetVec g t))
    (hh : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h t) t)
    (hhODE : ∀ t, iteratedDeriv n h t = Φ (jetVec h t))
    (hjet : jetVec (n := n) g t₀ = jetVec (n := n) h t₀) :
    jetVec (n := n) g = jetVec (n := n) h := by
  refine ODE_solution_unique_univ (K := max 1 K) (v := fun _ => companionField Φ)
    (s := fun _ => Set.univ) (t₀ := t₀) ?_ ?_ ?_ hjet
  · intro t
    exact (lipschitzWith_companionField hΦ).lipschitzOnWith
  · intro t
    exact ⟨hasDerivAt_jetVec hg (hgODE t), trivial⟩
  · intro t
    exact ⟨hasDerivAt_jetVec hh (hhODE t), trivial⟩

/-- The scalar consequence: two solutions with the same jet at one point are equal. -/
theorem eq_of_jetVec_eq_at {n : ℕ} (hn : 0 < n) {Φ : (Fin n → ℂ) → ℂ} {K : NNReal}
    (hΦ : LipschitzWith K Φ) {g h : ℝ → ℂ} {t₀ : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : ∀ t, iteratedDeriv n g t = Φ (jetVec g t))
    (hh : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h t) t)
    (hhODE : ∀ t, iteratedDeriv n h t = Φ (jetVec h t))
    (hjet : jetVec (n := n) g t₀ = jetVec (n := n) h t₀) : g = h := by
  have hall := jetVec_eq_of_eq_at hΦ hg hgODE hh hhODE hjet
  funext t
  have := congrFun (congrFun hall t) ⟨0, hn⟩
  simpa [jetVec] using this

theorem lipschitzOnWith_companionField {n : ℕ} {Φ : (Fin n → ℂ) → ℂ} {K : NNReal}
    {S : Set (Fin n → ℂ)} (hΦ : LipschitzOnWith K Φ S) :
    LipschitzOnWith (max 1 K) (companionField Φ) S := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have hbase : dist y y' ≤ (max 1 K : ℝ) * dist y y' := by
    have h1 : (1 : ℝ) ≤ (max 1 K : ℝ) := by exact_mod_cast le_max_left (1 : NNReal) K
    nlinarith [dist_nonneg (x := y) (y := y')]
  by_cases hi : (i : ℕ) + 1 < n
  · simp only [companionField, dif_pos hi]
    exact le_trans (dist_le_pi_dist y y' _) hbase
  · simp only [companionField, dif_neg hi]
    have hK : dist (Φ y) (Φ y') ≤ (K : ℝ) * dist y y' := hΦ.dist_le_mul y hy y' hy'
    have hKle : (K : ℝ) ≤ (max 1 K : ℝ) := by exact_mod_cast le_max_right (1 : NNReal) K
    calc dist (Φ y) (Φ y') ≤ (K : ℝ) * dist y y' := hK
      _ ≤ (max 1 K : ℝ) * dist y y' := mul_le_mul_of_nonneg_right hKle dist_nonneg

/-- **A finite jet determines a solution of an explicit equation, on a region where the right-hand
side is Lipschitz.** -/
theorem jetVec_eq_of_eq_at_on {n : ℕ} {Φ : (Fin n → ℂ) → ℂ} {K : NNReal} {S : Set (Fin n → ℂ)}
    (hΦ : LipschitzOnWith K Φ S) {g h : ℝ → ℂ} {t₀ : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : ∀ t, iteratedDeriv n g t = Φ (jetVec g t)) (hgS : ∀ t, jetVec (n := n) g t ∈ S)
    (hh : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h t) t)
    (hhODE : ∀ t, iteratedDeriv n h t = Φ (jetVec h t)) (hhS : ∀ t, jetVec (n := n) h t ∈ S)
    (hjet : jetVec (n := n) g t₀ = jetVec (n := n) h t₀) :
    jetVec (n := n) g = jetVec (n := n) h := by
  refine ODE_solution_unique_univ (K := max 1 K) (v := fun _ => companionField Φ)
    (s := fun _ => S) (t₀ := t₀) ?_ ?_ ?_ hjet
  · intro t
    exact lipschitzOnWith_companionField hΦ
  · intro t
    exact ⟨hasDerivAt_jetVec hg (hgODE t), hgS t⟩
  · intro t
    exact ⟨hasDerivAt_jetVec hh (hhODE t), hhS t⟩

/-- The scalar consequence on a region. -/
theorem eq_of_jetVec_eq_at_on {n : ℕ} (hn : 0 < n) {Φ : (Fin n → ℂ) → ℂ} {K : NNReal}
    {S : Set (Fin n → ℂ)} (hΦ : LipschitzOnWith K Φ S) {g h : ℝ → ℂ} {t₀ : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : ∀ t, iteratedDeriv n g t = Φ (jetVec g t)) (hgS : ∀ t, jetVec (n := n) g t ∈ S)
    (hh : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h t) t)
    (hhODE : ∀ t, iteratedDeriv n h t = Φ (jetVec h t)) (hhS : ∀ t, jetVec (n := n) h t ∈ S)
    (hjet : jetVec (n := n) g t₀ = jetVec (n := n) h t₀) : g = h := by
  have hall := jetVec_eq_of_eq_at_on hΦ hg hgODE hgS hh hhODE hhS hjet
  funext t
  have := congrFun (congrFun hall t) ⟨0, hn⟩
  simpa [jetVec] using this

section Local

/-- **Local jet separation.**  Two solutions of an explicit equation whose jets agree at a point and
run inside a region where the right-hand side is Lipschitz near that point agree near it. -/
theorem eventuallyEq_of_jetVec_eq_at {n : ℕ} (hn : 0 < n) {Φ : (Fin n → ℂ) → ℂ} {K : NNReal}
    {S : Set (Fin n → ℂ)} (hΦ : LipschitzOnWith K Φ S) {g h : ℝ → ℂ} {t₀ : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : ∀ᶠ t in nhds t₀, iteratedDeriv n g t = Φ (jetVec g t))
    (hgS : ∀ᶠ t in nhds t₀, jetVec (n := n) g t ∈ S)
    (hh : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h t) t)
    (hhODE : ∀ᶠ t in nhds t₀, iteratedDeriv n h t = Φ (jetVec h t))
    (hhS : ∀ᶠ t in nhds t₀, jetVec (n := n) h t ∈ S)
    (hjet : jetVec (n := n) g t₀ = jetVec (n := n) h t₀) :
    g =ᶠ[nhds t₀] h := by
  have hjets : jetVec (n := n) g =ᶠ[nhds t₀] jetVec (n := n) h := by
    refine ODE_solution_unique_of_eventually (K := max 1 K) (v := fun _ => companionField Φ)
      (s := fun _ => S) ?_ ?_ ?_ hjet
    · filter_upwards with t
      exact lipschitzOnWith_companionField hΦ
    · filter_upwards [hgS, hgODE] with t ht hode
      exact ⟨hasDerivAt_jetVec hg hode, ht⟩
    · filter_upwards [hhS, hhODE] with t ht hode
      exact ⟨hasDerivAt_jetVec hh hode, ht⟩
  filter_upwards [hjets] with t ht
  have := congrFun ht ⟨0, hn⟩
  simpa [jetVec] using this

end Local

end GaloisForLFunctions
