import Mathlib

/-!
# Radial affine torsor and the cross-prime flatness no-go

Two graded components of different weights carry a one-parameter family of cross-grade relation
lines, and the radial character group acts on that family freely and transitively: every member has
trivial stabilizer, so no radial-equivariant datum can select one.

For a profile of radial slopes indexed by primes, the radial gauge acts by `b_p ↦ b_p + c log p`.
The normalized differences `κ_pq = b_p/log p − b_q/log q` are complete gauge invariants: they
determine the orbit and nothing more.  In particular the cross-prime flat locus is a single full
orbit, and the Riemann slope profile `b_p(ρ) = (2 Re ρ − 1) log p` is flat for **every** `ρ`, on or
off the critical line.  Cross-prime curvature therefore cannot select the critical slope.
-/

namespace HTGeometry.ConstraintRelativity

open Real

/-! ## The two-grade radial torsor -/

section Torsor

variable {g h : ℝ}

/-- The cross-grade relation line of parameter `λ` inside a two-grade component. -/
noncomputable def gradeLine (lam : ℝ) : Submodule ℝ (ℝ × ℝ) :=
  Submodule.span ℝ {((1 : ℝ), lam)}

/-- The radial character action on a two-grade component. -/
noncomputable def radialAction (g h c : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ :=
  (LinearMap.fst ℝ ℝ ℝ |>.smulRight (g ^ c, (0 : ℝ)))
    + (LinearMap.snd ℝ ℝ ℝ |>.smulRight ((0 : ℝ), h ^ c))

@[simp]
theorem radialAction_apply (g h c : ℝ) (v : ℝ × ℝ) :
    radialAction g h c v = (g ^ c * v.1, h ^ c * v.2) := by
  simp only [radialAction, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_zero, add_zero,
    zero_add, mul_comm]

/-- **Card `(2)`.**  The radial action moves the relation line of parameter `λ` to the line of
parameter `λ (h/g)^c`. -/
theorem map_gradeLine (hg : 0 < g) (hh : 0 < h) (c lam : ℝ) :
    Submodule.map (radialAction g h c) (gradeLine lam) = gradeLine (lam * (h / g) ^ c) := by
  have hgc : (0 : ℝ) < g ^ c := Real.rpow_pos_of_pos hg c
  have hkey : radialAction g h c ((1 : ℝ), lam) = (g ^ c) • ((1 : ℝ), lam * (h / g) ^ c) := by
    rw [radialAction_apply]
    refine Prod.ext ?_ ?_
    · simp
    · show h ^ c * lam = g ^ c * (lam * (h / g) ^ c)
      rw [Real.div_rpow hh.le hg.le]
      field_simp
  rw [gradeLine, gradeLine, Submodule.map_span, Set.image_singleton, hkey,
    Submodule.span_singleton_smul_eq]
  exact (isUnit_iff_ne_zero.2 hgc.ne').unit.isUnit

/-- **Card `(2)`, transitivity.**  For distinct positive grades the radial parameter map is a
bijection of `ℝ` onto the positive parameters. -/
theorem exists_unique_radial_parameter (hg : 0 < g) (hh : 0 < h) (hgh : g ≠ h)
    {lam lam' : ℝ} (hlam : 0 < lam) (hlam' : 0 < lam') :
    ∃! c : ℝ, lam * (h / g) ^ c = lam' := by
  have hq : 0 < h / g := div_pos hh hg
  have hq1 : h / g ≠ 1 := by
    intro hcon
    exact hgh (by field_simp at hcon; linarith [hcon])
  have hlog : Real.log (h / g) ≠ 0 := by
    intro hcon
    apply hq1
    have hexp := Real.exp_log hq
    rw [hcon, Real.exp_zero] at hexp
    exact hexp.symm
  refine ⟨Real.log (lam' / lam) / Real.log (h / g), ?_, ?_⟩
  · show lam * (h / g) ^ (Real.log (lam' / lam) / Real.log (h / g)) = lam'
    have hexp : Real.log (h / g) * (Real.log (lam' / lam) / Real.log (h / g))
        = Real.log (lam' / lam) := by field_simp
    rw [Real.rpow_def_of_pos hq, hexp, Real.exp_log (div_pos hlam' hlam)]
    field_simp
  · intro c hc
    have hpow : (h / g) ^ c = lam' / lam := by
      field_simp at hc ⊢
      linarith [hc]
    have := congrArg Real.log hpow
    rw [Real.log_rpow hq] at this
    field_simp at this ⊢
    linarith [this]

/-- **Trivial stabilizer.**  Only the identity radial character fixes a relation line. -/
theorem radial_stabilizer_trivial (hg : 0 < g) (hh : 0 < h) (hgh : g ≠ h)
    {lam : ℝ} (hlam : 0 < lam) {c : ℝ} (hc : lam * (h / g) ^ c = lam) : c = 0 := by
  obtain ⟨d, _, huniq⟩ := exists_unique_radial_parameter hg hh hgh hlam hlam
  rw [huniq c hc, huniq 0 (by simp)]

end Torsor

/-! ## The cross-prime gauge invariant -/

section CrossPrime

variable {ι : Type*} (w : ι → ℝ)

/-- The radial gauge action on a slope profile: `b_p ↦ b_p + c log p`. -/
def slopeAction (c : ℝ) (b : ι → ℝ) : ι → ℝ := fun i => b i + c * w i

/-- The normalized cross-prime difference `κ_pq = b_p/log p − b_q/log q`. -/
noncomputable def crossCurvature (b : ι → ℝ) (i j : ι) : ℝ := b i / w i - b j / w j

/-- **Card `(5)`, invariance.**  The cross-prime curvature is gauge invariant. -/
theorem crossCurvature_slopeAction (hw : ∀ i, w i ≠ 0) (c : ℝ) (b : ι → ℝ) (i j : ι) :
    crossCurvature w (slopeAction w c b) i j = crossCurvature w b i j := by
  have hi := hw i
  have hj := hw j
  simp only [crossCurvature, slopeAction, add_div, mul_div_assoc, div_self hi, div_self hj,
    mul_one]
  ring

/-- **Card `(5)`, completeness.**  Two profiles with equal cross-prime curvatures lie in the same
radial orbit. -/
theorem exists_slopeAction_of_crossCurvature_eq (hw : ∀ i, w i ≠ 0) [Nonempty ι]
    {b b' : ι → ℝ} (hk : ∀ i j, crossCurvature w b i j = crossCurvature w b' i j) :
    ∃ c : ℝ, b' = slopeAction w c b := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨b' i₀ / w i₀ - b i₀ / w i₀, ?_⟩
  funext i
  have h := hk i i₀
  simp only [crossCurvature] at h
  simp only [slopeAction]
  have hwi := hw i
  have hkey : b' i / w i = b i / w i + (b' i₀ / w i₀ - b i₀ / w i₀) := by linarith [h]
  have hmul := congrArg (fun t : ℝ => t * w i) hkey
  simp only [add_mul, div_mul_cancel₀ _ hwi] at hmul
  exact hmul

/-- **Card `(6)`–`(7)`.**  A profile is cross-prime flat exactly when it is a radial multiple of
the weight, so the flat locus is one full orbit rather than a point. -/
theorem crossCurvature_eq_zero_iff (hw : ∀ i, w i ≠ 0) [Nonempty ι] (b : ι → ℝ) :
    (∀ i j, crossCurvature w b i j = 0) ↔ ∃ a : ℝ, ∀ i, b i = a * w i := by
  classical
  constructor
  · intro hflat
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨b i₀ / w i₀, fun i => ?_⟩
    have h := hflat i i₀
    simp only [crossCurvature, sub_eq_zero] at h
    have hwi := hw i
    have hmul := congrArg (fun t : ℝ => t * w i) h
    simp only [div_mul_cancel₀ _ hwi] at hmul
    rw [← hmul]
  · rintro ⟨a, ha⟩ i j
    simp only [crossCurvature, ha i, ha j]
    rw [mul_div_assoc, mul_div_assoc, div_self (hw i), div_self (hw j)]
    ring

/-- **Card `(8)`.**  The Riemann slope profile is cross-prime flat for **every** `ρ`, on or off the
critical line: cross-prime curvature cannot select the critical slope. -/
theorem riemannProfile_flat (hw : ∀ i, w i ≠ 0) (rho : ℂ) (i j : ι) :
    crossCurvature w (fun k => (2 * rho.re - 1) * w k) i j = 0 := by
  simp only [crossCurvature]
  rw [mul_div_assoc, mul_div_assoc, div_self (hw i), div_self (hw j)]
  ring

end CrossPrime

/-! ## The prime instance -/

/-- Prime logarithms are nonzero, so the general theory applies to the prime-indexed profile with
no extra hypothesis. -/
theorem log_prime_ne_zero {p : ℕ} (hp : p.Prime) : Real.log (p : ℝ) ≠ 0 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  exact hpos.ne'

/-- The cross-prime curvature of the Riemann slope profile vanishes at every `ρ`. -/
theorem riemannProfile_prime_flat (P : Type*) (p : P → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ)
    (i j : P) :
    crossCurvature (fun k => Real.log (p k : ℝ))
      (fun k => (2 * rho.re - 1) * Real.log (p k : ℝ)) i j = 0 :=
  riemannProfile_flat _ (fun k => log_prime_ne_zero (hp k)) rho i j

end HTGeometry.ConstraintRelativity
