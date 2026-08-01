import GaloisForLFunctions.HTGeometry.ODEJetSeparation
import GaloisForLFunctions.HTGeometry.LineJetTransfer
import GaloisForLFunctions.HTGeometry.ImplicitLipschitzGraph

/-!
# Finite jets separate holomorphic solutions on a strip

A holomorphic solution of an explicit equation `y⁽ⁿ⁾ = Φ(y, …, y⁽ⁿ⁻¹⁾)` on a vertical strip restricts
on the central line to a solution of the same equation in the real parameter, with the right-hand
side twisted by powers of `i`; the twist is an isometry, so the twisted field is Lipschitz whenever
`Φ` is.  Uniqueness for Lipschitz ODEs then makes the order-`n` jet at a single point of the line
determine the restriction, and the identity theorem promotes that to the whole strip.

This is the separation statement behind the finite jet embedding of the phase carrier: all carrier
points solve the same equation, so a finite jet sample distinguishes them.
-/

open Filter Topology Metric Set

namespace GaloisForLFunctions

variable {σ R : ℝ}

/-- The twisted right-hand side of the explicit equation satisfied by a line restriction. -/
noncomputable def twistField {n : ℕ} (Φ : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun y => Complex.I ^ n * Φ (fun k => (Complex.I ^ (k : ℕ))⁻¹ * y k)

theorem lipschitzWith_twistField {n : ℕ} {Φ : (Fin n → ℂ) → ℂ} {K : NNReal}
    (hΦ : LipschitzWith K Φ) : LipschitzWith K (twistField Φ) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  set a : Fin n → ℂ := fun k => (Complex.I ^ (k : ℕ))⁻¹ * y k with ha
  set a' : Fin n → ℂ := fun k => (Complex.I ^ (k : ℕ))⁻¹ * y' k with ha'
  have hnorm : ∀ k : Fin n, ‖(Complex.I ^ (k : ℕ))⁻¹‖ = 1 := by
    intro k
    rw [norm_inv, norm_pow, Complex.norm_I, one_pow, inv_one]
  have hle : dist a a' ≤ dist y y' := by
    rw [dist_pi_le_iff dist_nonneg]
    intro k
    have hk : dist (a k) (a' k) = dist (y k) (y' k) := by
      show dist ((Complex.I ^ (k : ℕ))⁻¹ * y k) ((Complex.I ^ (k : ℕ))⁻¹ * y' k)
        = dist (y k) (y' k)
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hnorm k, one_mul]
    rw [hk]
    exact dist_le_pi_dist y y' k
  calc dist (twistField Φ y) (twistField Φ y') = dist (Φ a) (Φ a') := by
        show dist (Complex.I ^ n * Φ a) (Complex.I ^ n * Φ a') = dist (Φ a) (Φ a')
        rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, norm_pow, Complex.norm_I, one_pow,
          one_mul]
    _ ≤ K * dist a a' := hΦ.dist_le_mul a a'
    _ ≤ K * dist y y' := mul_le_mul_of_nonneg_left hle (by positivity)

/-- The line restriction of a holomorphic function has the expected derivative chain. -/
theorem hasDerivAt_iteratedDeriv_line {g : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (i : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv i (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)))
      (iteratedDeriv (i + 1) (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t) t := by
  have hjd : DifferentiableOn ℂ (iteratedDeriv i g) (verticalStrip σ R) :=
    differentiableOn_iteratedDeriv_verticalStrip hg i
  have hfun : (iteratedDeriv i fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I))
      = fun s : ℝ => Complex.I ^ i * iteratedDeriv i g ((σ : ℂ) + (s : ℂ) * Complex.I) := by
    funext s
    exact iteratedDeriv_line_restriction hR hg i s
  have hval : iteratedDeriv (i + 1) (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t
      = Complex.I ^ i * (Complex.I * deriv (iteratedDeriv i g) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [iteratedDeriv_line_restriction hR hg (i + 1) t, iteratedDeriv_succ]
    ring
  rw [hfun, hval]
  exact (hasDerivAt_line_restriction hR hjd t).const_mul _

/-- The line restriction solves the twisted explicit equation. -/
theorem iteratedDeriv_line_eq_twist {g : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) {n : ℕ} {Φ : (Fin n → ℂ) → ℂ} {t : ℝ}
    (hgODE : iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    iteratedDeriv n (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t
      = twistField Φ (jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t) := by
  have hleft : iteratedDeriv n (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t
      = Complex.I ^ n * iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    iteratedDeriv_line_restriction hR hg n t
  have hjet : ∀ k : Fin n, (Complex.I ^ (k : ℕ))⁻¹
      * jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t k
      = iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro k
    have hk : jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hg (k : ℕ) t
    rw [hk, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]
  have hfun : (fun k : Fin n => (Complex.I ^ (k : ℕ))⁻¹
      * jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t k)
      = fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    funext k
    exact hjet k
  rw [hleft, hgODE, twistField, hfun]

/-- **Finite jets on the central line separate holomorphic solutions on the strip.** -/
theorem eqOn_of_line_jet_eq {g h : ℂ → ℂ} (hR : 0 < R) {n : ℕ} (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {Φ : (Fin n → ℂ) → ℂ} {K : NNReal} (hΦ : LipschitzWith K Φ)
    (hgODE : ∀ t : ℝ, iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hhODE : ∀ t : ℝ, iteratedDeriv n h ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I))
    {t₀ : ℝ}
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  have hline : (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I))
      = fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I) := by
    refine eq_of_jetVec_eq_at hn (lipschitzWith_twistField hΦ) (t₀ := t₀)
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hg i t)
      (fun t => iteratedDeriv_line_eq_twist hR hg (hgODE t))
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hh i t)
      (fun t => iteratedDeriv_line_eq_twist hR hh (hhODE t)) ?_
    funext k
    have hk1 : jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hg (k : ℕ) t₀
    have hk2 : jetVec (fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hh (k : ℕ) t₀
    rw [hk1, hk2, hjet k]
  exact eqOn_of_eqOn_line hR hg hh (fun t => congrFun hline t)

/-- The isometric twist relating complex jets to line jets. -/
noncomputable def twistMap {n : ℕ} : (Fin n → ℂ) → (Fin n → ℂ) :=
  fun y k => (Complex.I ^ (k : ℕ))⁻¹ * y k

theorem dist_twistMap {n : ℕ} (y y' : Fin n → ℂ) : dist (twistMap y) (twistMap y') = dist y y' := by
  have hnorm : ∀ k : Fin n, ‖(Complex.I ^ (k : ℕ))⁻¹‖ = 1 := by
    intro k
    rw [norm_inv, norm_pow, Complex.norm_I, one_pow, inv_one]
  refine le_antisymm ?_ ?_
  · rw [dist_pi_le_iff dist_nonneg]
    intro k
    have hk : dist (twistMap y k) (twistMap y' k) = dist (y k) (y' k) := by
      show dist ((Complex.I ^ (k : ℕ))⁻¹ * y k) ((Complex.I ^ (k : ℕ))⁻¹ * y' k)
        = dist (y k) (y' k)
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hnorm k, one_mul]
    rw [hk]
    exact dist_le_pi_dist y y' k
  · rw [dist_pi_le_iff dist_nonneg]
    intro k
    have hk : dist (y k) (y' k) = dist (twistMap y k) (twistMap y' k) := by
      show dist (y k) (y' k)
        = dist ((Complex.I ^ (k : ℕ))⁻¹ * y k) ((Complex.I ^ (k : ℕ))⁻¹ * y' k)
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hnorm k, one_mul]
    rw [hk]
    exact dist_le_pi_dist (twistMap y) (twistMap y') k

theorem lipschitzOnWith_twistField {n : ℕ} {Φ : (Fin n → ℂ) → ℂ} {K : NNReal}
    {S : Set (Fin n → ℂ)} (hΦ : LipschitzOnWith K Φ S) :
    LipschitzOnWith K (twistField Φ) (twistMap ⁻¹' S) := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
  have hval : ∀ w : Fin n → ℂ, twistField Φ w = Complex.I ^ n * Φ (twistMap w) := fun w => rfl
  rw [hval, hval, dist_eq_norm, ← mul_sub, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
    ← dist_eq_norm]
  calc dist (Φ (twistMap y)) (Φ (twistMap y')) ≤ (K : ℝ) * dist (twistMap y) (twistMap y') :=
        hΦ.dist_le_mul _ hy _ hy'
    _ = (K : ℝ) * dist y y' := by rw [dist_twistMap]

/-- **Finite jets separate holomorphic solutions on a strip, on a region where the explicit
right-hand side is Lipschitz.** -/
theorem eqOn_of_line_jet_eq_on {g h : ℂ → ℂ} (hR : 0 < R) {n : ℕ} (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {Φ : (Fin n → ℂ) → ℂ} {K : NNReal} {S : Set (Fin n → ℂ)} (hΦ : LipschitzOnWith K Φ S)
    (hgODE : ∀ t : ℝ, iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hgS : ∀ t : ℝ, (fun k : Fin n => iteratedDeriv (k : ℕ) g
      ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hhODE : ∀ t : ℝ, iteratedDeriv n h ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hhS : ∀ t : ℝ, (fun k : Fin n => iteratedDeriv (k : ℕ) h
      ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    {t₀ : ℝ}
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  have htwist : ∀ (u : ℂ → ℂ), DifferentiableOn ℂ u (verticalStrip σ R) → ∀ t : ℝ,
      twistMap (jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t)
        = fun k : Fin n => iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro u hu t
    funext k
    have hk : jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hu (k : ℕ) t
    show (Complex.I ^ (k : ℕ))⁻¹ * jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t k
      = iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I)
    rw [hk, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]
  have hline : (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I))
      = fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I) := by
    refine eq_of_jetVec_eq_at_on hn (lipschitzOnWith_twistField hΦ) (t₀ := t₀)
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hg i t)
      (fun t => iteratedDeriv_line_eq_twist hR hg (hgODE t))
      (fun t => by
        show twistMap (jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t) ∈ S
        rw [htwist g hg t]
        exact hgS t)
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hh i t)
      (fun t => iteratedDeriv_line_eq_twist hR hh (hhODE t))
      (fun t => by
        show twistMap (jetVec (fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I)) t) ∈ S
        rw [htwist h hh t]
        exact hhS t) ?_
    funext k
    have hk1 : jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hg (k : ℕ) t₀
    have hk2 : jetVec (fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hh (k : ℕ) t₀
    rw [hk1, hk2, hjet k]
  exact eqOn_of_eqOn_line hR hg hh (fun t => congrFun hline t)

section Implicit

variable {σ R : ℝ} {n : ℕ}

/-- **Jet separation from an implicit relation.**  Two holomorphic functions on a strip whose
`(n+1)`-jets along the central line solve the same relation inside a region where the top partial
derivative dominates, and whose `n`-jets agree at one point, agree on the strip. -/
theorem eqOn_of_line_jet_eq_implicit {g h : ℂ → ℂ} (hR : 0 < R) (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) (hP : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
    {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y ∈ S, ‖P' y - L‖ ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖)
    (hgS : ∀ t : ℝ, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hgP : ∀ t : ℝ, P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hhS : ∀ t : ℝ, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hhP : ∀ t : ℝ, P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    {t₀ : ℝ}
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  obtain ⟨Φ, K, hΦlip, hΦval⟩ := exists_lipschitz_implicit hS hP hC hbound hdom
  have hgODE : ∀ t : ℝ, iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    have hval := hΦval _ (hgS t) (hgP t)
    simpa using hval
  have hhODE : ∀ t : ℝ, iteratedDeriv n h ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    have hval := hΦval _ (hhS t) (hhP t)
    simpa using hval
  exact eqOn_of_line_jet_eq hR hn hg hh hΦlip hgODE hhODE hjet

end Implicit

section LocalSeparation

variable {σ R : ℝ} {n : ℕ}

/-- **Local jet separation on a strip.**  Two holomorphic solutions of the same explicit equation
whose jets agree at one point of the central line, and whose jets run inside the Lipschitz region
only near that point, agree on the whole strip. -/
theorem eqOn_of_line_jet_eq_local {g h : ℂ → ℂ} (hR : 0 < R) (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {Φ : (Fin n → ℂ) → ℂ} {K : NNReal} {S : Set (Fin n → ℂ)} (hΦ : LipschitzOnWith K Φ S)
    {t₀ : ℝ}
    (hgODE : ∀ᶠ t : ℝ in nhds t₀, iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hhODE : ∀ᶠ t : ℝ in nhds t₀, iteratedDeriv n h ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ fun k : Fin n => iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hgS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin n =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hhS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin n =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  have htwist : ∀ (u : ℂ → ℂ), DifferentiableOn ℂ u (verticalStrip σ R) → ∀ t : ℝ,
      twistMap (jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t)
        = fun k : Fin n => iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro u hu t
    funext k
    have hk : jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hu (k : ℕ) t
    show (Complex.I ^ (k : ℕ))⁻¹ * jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t k
      = iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I)
    rw [hk, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]
  have hline : (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I))
      =ᶠ[nhds t₀] fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I) := by
    refine eventuallyEq_of_jetVec_eq_at hn (lipschitzOnWith_twistField hΦ)
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hg i t) ?_ ?_
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hh i t) ?_ ?_ ?_
    · filter_upwards [hgODE] with t ht
      exact iteratedDeriv_line_eq_twist hR hg ht
    · filter_upwards [hgS] with t ht
      show twistMap (jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t) ∈ S
      rw [htwist g hg t]
      exact ht
    · filter_upwards [hhODE] with t ht
      exact iteratedDeriv_line_eq_twist hR hh ht
    · filter_upwards [hhS] with t ht
      show twistMap (jetVec (fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I)) t) ∈ S
      rw [htwist h hh t]
      exact ht
    · funext k
      have hk1 : jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
          = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
        iteratedDeriv_line_restriction hR hg (k : ℕ) t₀
      have hk2 : jetVec (fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
          = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
        iteratedDeriv_line_restriction hR hh (k : ℕ) t₀
      rw [hk1, hk2, hjet k]
  exact eqOn_of_eventuallyEq_line hR hg hh hline

/-- **Local jet separation from an implicit relation.**  Regularity of the relation near one sample
time suffices: two holomorphic solutions whose jets agree there agree on the whole strip. -/
theorem eqOn_of_line_jet_eq_implicit_local {g h : ℂ → ℂ} (hR : 0 < R) (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) (hPd : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
    {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y ∈ S, ‖P' y - L‖ ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖) {t₀ : ℝ}
    (hgS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hgP : ∀ᶠ t : ℝ in nhds t₀, P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hhS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hhP : ∀ᶠ t : ℝ in nhds t₀, P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  obtain ⟨Φ, K, hΦlip, hΦval⟩ := exists_lipschitz_implicit hS hPd hC hbound hdom
  have hODE : ∀ (u : ℂ → ℂ),
      (∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S) →
      (∀ᶠ t : ℝ in nhds t₀, P (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0) →
      ∀ᶠ t : ℝ in nhds t₀, iteratedDeriv n u ((σ : ℂ) + (t : ℂ) * Complex.I)
        = Φ fun k : Fin n => iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro u huS huP
    filter_upwards [huS, huP] with t hS' hP'
    have hval := hΦval _ hS' hP'
    simpa using hval
  exact eqOn_of_line_jet_eq_local hR hn hg hh (S := Set.univ) (hΦlip.lipschitzOnWith)
    (hODE g hgS hgP) (hODE h hhS hhP)
    (Filter.Eventually.of_forall fun t => Set.mem_univ _)
    (Filter.Eventually.of_forall fun t => Set.mem_univ _) hjet

end LocalSeparation

end GaloisForLFunctions
