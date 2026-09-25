import GaloisForLFunctions.RHTower.ClockDegeneracy

/-!
# The marginality identity: transverse Coulomb equilibrium

Under the heat deformation the zeros move by a Calogero flow, and taking real parts of
`ż_j = 2 Σ_{k≠j}(z_j − z_k)⁻¹` shows that the **displacement** `δ_ρ = Re ρ − 1/2` evolves by the
**graph heat equation**

  `δ̇_j = −(Δδ)_j`,   `(Δδ)_j = Σ_{k≠j} (δ_j − δ_k)/|ρ_j − ρ_k|²`,

on the graph whose vertices are the zeros and whose conductances are `1/|ρ_j − ρ_k|²`.  So the
hypothesis — all displacements zero — is an **equilibrium** of that flow, and the critical-point
diagnosis of `CANNOT-411` becomes concrete: the marginality condition is that the equilibrium is
attained exactly, i.e. that the **transverse Coulomb force on every zero vanishes**:

  `Σ_{ρ' ≠ ρ} (Re ρ − Re ρ')/|ρ − ρ'|² = 0`.

This is an *identity*, not a bound — the shape `CANNOT-411` says a producer must have.  It is the
Euler–Lagrange equation of the transverse Dirichlet energy `½ Σ (δ_j − δ_k)²/|ρ_j − ρ_k|²`, which is
exactly the energy the heat flow dissipates.

The Liouville chain it sits in: *harmonic* (this identity) + *bounded* (the strip) + *recurrent* (the
zero graph, from Riemann–von Mangoldt) forces the displacement to be **constant**, and constancy
forces the hypothesis by the functional equation.  The last step is proved here:

  `riemannHypothesis_iff_re_constant : RiemannHypothesis ↔ ∃ c, ∀ ρ, Re ρ = c`.

Also proved: the force term of a zero against its own reflection partner is exactly `1/(2δ)`, so the
identity makes the partner's transverse repulsion diverge as the displacement shrinks and forces the
remaining zeros to balance it.
-/

open Complex Set

namespace RHTower

noncomputable section

/-! ## Constancy of the displacement is the hypothesis -/

/-- **If the real part is constant on the divisor, the hypothesis holds.**  The functional equation
pins the constant to one half. -/
theorem riemannHypothesis_of_forall_re_eq {c : ℝ}
    (h : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = c) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_supportPartner_eq_id]
  intro ρ
  rw [supportPartner_eq_self_iff]
  have h1 := h ρ
  have h2 := h (supportPartner ρ)
  rw [supportPartner_re, h1] at h2
  linarith

/-- **The hypothesis is the constancy of the displacement.**  This is the Liouville-shaped form of
the hypothesis: a bounded harmonic function on a recurrent graph is constant, and constancy is the
hypothesis. -/
theorem riemannHypothesis_iff_re_constant :
    RiemannHypothesis ↔ ∃ c : ℝ, ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = c := by
  constructor
  · intro hRH
    refine ⟨1 / 2, fun ρ => ?_⟩
    exact (supportPartner_eq_self_iff ρ).mp
      (riemannHypothesis_iff_supportPartner_eq_id.mp hRH ρ)
  · rintro ⟨c, hc⟩
    exact riemannHypothesis_of_forall_re_eq hc

/-! ## The transverse Coulomb force -/

/-- The transverse force exerted on the zero `j` by the zero `k`: the real part of `1/(ρ_j − ρ_k)`.
-/
def transverseForceTerm (j k : XiDivisorSupport) : ℝ :=
  if k = j then 0
  else ((j : ℂ).re - (k : ℂ).re) / Complex.normSq ((j : ℂ) - (k : ℂ))

/-- The total transverse force on a zero: the graph Laplacian of the displacement. -/
def transverseForce (j : XiDivisorSupport) : ℝ := ∑' k : XiDivisorSupport, transverseForceTerm j k

/-- Under the hypothesis every individual transverse force term vanishes: distinct zeros share a
real part, so there is no transverse component at all. -/
theorem transverseForceTerm_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    (j k : XiDivisorSupport) : transverseForceTerm j k = 0 := by
  unfold transverseForceTerm
  split_ifs with h
  · rfl
  · obtain ⟨c, hc⟩ := riemannHypothesis_iff_re_constant.mp hRH
    rw [hc j, hc k, sub_self, zero_div]

/-- **The marginality identity holds under the hypothesis.** -/
theorem transverseForce_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    (j : XiDivisorSupport) : transverseForce j = 0 := by
  unfold transverseForce
  simp only [transverseForceTerm_eq_zero_of_riemannHypothesis hRH]
  exact tsum_zero

/-! ## The partner term -/

/-- The difference between a zero and its reflection partner is the real number `2 Re ρ − 1`. -/
theorem sub_supportPartner_eq (ρ : XiDivisorSupport) :
    ((ρ : ℂ)) - ((supportPartner ρ : XiDivisorSupport) : ℂ) = ((2 * (ρ : ℂ).re - 1 : ℝ) : ℂ) := by
  rw [supportPartner_coe]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.ofReal_re]
    ring
  · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, Complex.ofReal_im]
    ring

/-- **The partner's transverse force is exactly `1/(2δ)`**, with `δ = Re ρ − 1/2` the displacement:
an off-line zero is pushed by its own reflection with a force that diverges as it approaches the
critical line.  The marginality identity therefore forces the remaining zeros to balance it. -/
theorem transverseForceTerm_supportPartner {ρ : XiDivisorSupport}
    (h : supportPartner ρ ≠ ρ) :
    transverseForceTerm ρ (supportPartner ρ) = 1 / (2 * (ρ : ℂ).re - 1) := by
  have hre : (ρ : ℂ).re ≠ 1 / 2 := fun hc => h ((supportPartner_eq_self_iff ρ).mpr hc)
  have hd : (2 * (ρ : ℂ).re - 1) ≠ 0 := by
    intro hc; apply hre; linarith
  unfold transverseForceTerm
  rw [if_neg h, sub_supportPartner_eq ρ, supportPartner_re]
  rw [Complex.normSq_ofReal]
  have hnum : (ρ : ℂ).re - (1 - (ρ : ℂ).re) = 2 * (ρ : ℂ).re - 1 := by ring
  rw [hnum]
  field_simp

end

end RHTower
