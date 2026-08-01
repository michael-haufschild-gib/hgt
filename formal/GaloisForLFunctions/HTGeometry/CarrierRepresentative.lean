import GaloisForLFunctions.HTGeometry.LineStripCarrier
import GaloisForLFunctions.HTGeometry.StripRelationPropagation
import GaloisForLFunctions.HTGeometry.JetSampleAtlas

/-!
# Holomorphic representatives of carrier points, and their separation by jets

A point of the carrier of the line restriction maps to a point of the strip carrier, which *is* a
holomorphic function on the substrip solving the same relation; reading that function on the central
line recovers the evaluations of the original carrier point.  So every carrier point has a
holomorphic representative, canonically compatible with the carrier structure.

Two carrier points whose representatives have equal jets at one point of the line — inside a region
where the top partial derivative of the relation dominates — have equal representatives, hence equal
evaluations along the line, hence are equal.  This is the separation hypothesis that the finite jet
atlas consumes.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {F : ℂ → ℂ} {σ R r : ℝ}

theorem mem_closedStrip_line (hr : 0 ≤ r) (σ : ℝ) (t : ℝ) :
    ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ closedStrip σ r := by
  show |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| ≤ r
  have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  rw [this]
  simpa using hr

/-- The strip evaluation of the image of a line-carrier point, read on the central line, is the
line evaluation. -/
theorem bohrEval_strip_line (hr : 0 ≤ r)
    {f : ℝ →ᵇ ℂ} (_hfu : UniformContinuous (fun x => f x))
    (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    {ν : BohrHull f → BohrHull Gb} (hν : Continuous ν)
    (hνι : ∀ t : ℝ, ν (bohrIota f t) = bohrIota Gb t) (t : ℝ) (x : BohrHull f) :
    bohrEval Gb (ν x) ⟨(σ : ℂ) + (t : ℂ) * Complex.I, mem_closedStrip_line hr σ t⟩
      = bohrEval f (x + bohrIota f t) := by
  have hcont1 : Continuous fun x : BohrHull f =>
      bohrEval Gb (ν x) ⟨(σ : ℂ) + (t : ℂ) * Complex.I, mem_closedStrip_line hr σ t⟩ := by
    have h1 : Continuous fun x : BohrHull f => bohrEval Gb (ν x) :=
      (continuous_bohrEval Gb).comp hν
    exact (ContinuousEvalConst.continuous_eval_const _).comp h1
  have hcont2 : Continuous fun x : BohrHull f => bohrEval f (x + bohrIota f t) :=
    (continuous_bohrEval f).comp (continuous_id.add continuous_const)
  refine congrFun (Continuous.ext_on (denseRange_bohrIota f) hcont1 hcont2 ?_) x
  rintro y ⟨s, rfl⟩
  show bohrEval Gb (ν (bohrIota f s)) ⟨(σ : ℂ) + (t : ℂ) * Complex.I, _⟩
    = bohrEval f (bohrIota f s + bohrIota f t)
  rw [hνι s, bohrEval_bohrIota, ← bohrIota_add, bohrEval_bohrIota, hGb s, hf (s + t)]
  push_cast
  ring_nf

/-- **Every line-carrier point has a holomorphic representative solving the relation.** -/
theorem exists_holomorphic_rep (hr : r < R) (hr0 : 0 ≤ r)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    {n : ℕ} {P : (Fin n → ℂ) → ℂ} (hP : Continuous P)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k => iteratedDeriv (k : ℕ) F z) = 0)
    {f : ℝ →ᵇ ℂ} (hfu : UniformContinuous (fun x => f x))
    (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    {ν : BohrHull f → BohrHull Gb} (hν : Continuous ν)
    (hνι : ∀ t : ℝ, ν (bohrIota f t) = bohrIota Gb t) (x : BohrHull f) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ r) ∧
      (∀ z : closedStrip σ r, g (z : ℂ) = bohrEval Gb (ν x) z) ∧
      (∀ t : ℝ, g ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t)) ∧
        ∀ z ∈ verticalStrip σ r, P (fun k => iteratedDeriv (k : ℕ) g z) = 0 := by
  obtain ⟨g, hgdiff, hgval, hgrel⟩ := exists_solution_of_hull hr hF hP hrel hGb (ν x)
  refine ⟨g, hgdiff, hgval, fun t => ?_, hgrel⟩
  have h := hgval ⟨(σ : ℂ) + (t : ℂ) * Complex.I, mem_closedStrip_line hr0 σ t⟩
  rw [h]
  exact bohrEval_strip_line hr0 hfu hf hGb hν hνι t x

/-- **Regular jets separate carrier points.**  If the representatives of two carrier points solve
the same relation inside a region where the top partial derivative dominates, and their jets agree at
one point of the line, the carrier points coincide. -/
theorem carrier_eq_of_jet_eq (_hr : r < R) (_hr0 : 0 ≤ r) (hRpos : 0 < r)
    {f : ℝ →ᵇ ℂ} (hfu : UniformContinuous (fun x => f x))
    {n : ℕ} (hn : 0 < n) {g h : ℂ → ℂ}
    (hgdiff : DifferentiableOn ℂ g (verticalStrip σ r))
    (hhdiff : DifferentiableOn ℂ h (verticalStrip σ r))
    {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) (hPd : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
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
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I))
    {x y : BohrHull f}
    (hgx : ∀ t : ℝ, g ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (hhy : ∀ t : ℝ, h ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (y + bohrIota f t)) :
    x = y := by
  have heq : Set.EqOn g h (verticalStrip σ r) :=
    eqOn_of_line_jet_eq_implicit hRpos hn hgdiff hhdiff hS hPd hC hbound hdom hgS hgP hhS hhP hjet
  refine bohrHull_ext hfu fun t => ?_
  have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ verticalStrip σ r := by
    show |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| < r
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hre]
    simpa using hRpos
  have h := heq hmem
  rw [hgx t, hhy t] at h
  exact h

section JetContinuity

variable {ρ : ℝ}

/-- **The jet of a representative is Lipschitz in the substrip sup-distance.**  Two holomorphic
functions given by bounded continuous functions on a substrip have jets differing by at most the
Cauchy factor times the sup-distance of those functions. -/
theorem norm_jet_sub_le_dist (hρ : 0 < ρ) (hr : r + ρ < R)
    {g h : ℂ → ℂ} (hgdiff : DifferentiableOn ℂ g (verticalStrip σ R))
    (hhdiff : DifferentiableOn ℂ h (verticalStrip σ R))
    {u v : (closedStrip σ (r + ρ)) →ᵇ ℂ}
    (hgval : ∀ z : closedStrip σ (r + ρ), g (z : ℂ) = u z)
    (hhval : ∀ z : closedStrip σ (r + ρ), h (z : ℂ) = v z)
    (k : ℕ) : ∀ z ∈ closedStrip σ r,
      ‖iteratedDeriv k g z - iteratedDeriv k h z‖ ≤ (k.factorial : ℝ) * dist u v / ρ ^ k := by
  refine norm_iteratedDeriv_sub_le hρ hr hgdiff hhdiff ?_ k
  intro z hz
  have hzz : z = ((⟨z, hz⟩ : closedStrip σ (r + ρ)) : ℂ) := rfl
  rw [hgval ⟨z, hz⟩, hhval ⟨z, hz⟩, ← dist_eq_norm]
  exact BoundedContinuousFunction.dist_coe_le_dist _

end JetContinuity

/-- Continuity of a jet coordinate along a family of representatives. -/
theorem continuous_jet_of_representatives (hρ : 0 < ρ) (hrpos : 0 < r) (_hlt : r < r + ρ)
    {f : ℝ →ᵇ ℂ} {Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ℂ)}
    {ν : BohrHull f → BohrHull Gb} (hν : Continuous ν)
    {rep : BohrHull f → (ℂ → ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepval : ∀ (x : BohrHull f) (z : closedStrip σ (r + ρ)),
      rep x (z : ℂ) = bohrEval Gb (ν x) z)
    (k : ℕ) (t : ℝ) :
    Continuous fun x : BohrHull f =>
      iteratedDeriv k (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  have hEcont : Continuous fun x : BohrHull f => bohrEval Gb (ν x) :=
    (continuous_bohrEval Gb).comp hν
  have hbound : ∀ x y : BohrHull f,
      ‖iteratedDeriv k (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)
        - iteratedDeriv k (rep y) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (k.factorial : ℝ) * dist (bohrEval Gb (ν x)) (bohrEval Gb (ν y)) / r ^ k := by
    intro x y
    have hpt : ∀ z ∈ closedStrip σ (0 + r), ‖rep x z - rep y z‖
        ≤ dist (bohrEval Gb (ν x)) (bohrEval Gb (ν y)) := by
      intro z hz
      have hz' : z ∈ closedStrip σ (r + ρ) := by
        show |z.re - σ| ≤ r + ρ
        have : |z.re - σ| ≤ 0 + r := hz
        linarith
      rw [hrepval x ⟨z, hz'⟩, hrepval y ⟨z, hz'⟩, ← dist_eq_norm]
      exact BoundedContinuousFunction.dist_coe_le_dist _
    have hmain := norm_iteratedDeriv_sub_le (σ := σ) (r := 0) (ρ := r) (R := r + ρ)
      hrpos (by linarith) (hrepdiff x) (hrepdiff y) hpt k
    exact hmain _ (by
      show |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| ≤ 0
      have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      rw [hre]
      simp)
  refine Metric.continuous_iff.mpr fun x ε hε => ?_
  have hkpos : (0:ℝ) < (k.factorial : ℝ) / r ^ k := by positivity
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuous_iff.mp hEcont x (ε / ((k.factorial : ℝ) / r ^ k))
    (by positivity)
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have h1 := hδ y hy
  have h2 := hbound y x
  rw [dist_eq_norm]
  have hrw : (k.factorial : ℝ) * dist (bohrEval Gb (ν y)) (bohrEval Gb (ν x)) / r ^ k
      = ((k.factorial : ℝ) / r ^ k) * dist (bohrEval Gb (ν y)) (bohrEval Gb (ν x)) := by
    field_simp
  rw [hrw] at h2
  calc ‖iteratedDeriv k (rep y) ((σ : ℂ) + (t : ℂ) * Complex.I)
      - iteratedDeriv k (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((k.factorial : ℝ) / r ^ k) * dist (bohrEval Gb (ν y)) (bohrEval Gb (ν x)) := h2
    _ < ((k.factorial : ℝ) / r ^ k) * (ε / ((k.factorial : ℝ) / r ^ k)) := by
        exact mul_lt_mul_of_pos_left h1 hkpos
    _ = ε := by field_simp

section LocalSeparation

variable {n : ℕ}

/-- **Regular jets separate carrier points, locally.**  Only regularity near the sample time is
needed. -/
theorem carrier_eq_of_jet_eq_local (hrpos : 0 < r)
    {f : ℝ →ᵇ ℂ} (hfu : UniformContinuous (fun x => f x)) (hn : 0 < n) {g h : ℂ → ℂ}
    (hgdiff : DifferentiableOn ℂ g (verticalStrip σ r))
    (hhdiff : DifferentiableOn ℂ h (verticalStrip σ r))
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
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I))
    {x y : BohrHull f}
    (hgx : ∀ t : ℝ, g ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (hhy : ∀ t : ℝ, h ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (y + bohrIota f t)) :
    x = y := by
  have heq : Set.EqOn g h (verticalStrip σ r) :=
    eqOn_of_line_jet_eq_implicit_local hrpos hn hgdiff hhdiff hS hPd hC hbound hdom
      hgS hgP hhS hhP hjet
  refine bohrHull_ext hfu fun t => ?_
  have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ verticalStrip σ r := by
    show |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| < r
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hre]
    simpa using hrpos
  have hval := heq hmem
  rw [hgx t, hhy t] at hval
  exact hval

end LocalSeparation

end GaloisForLFunctions
