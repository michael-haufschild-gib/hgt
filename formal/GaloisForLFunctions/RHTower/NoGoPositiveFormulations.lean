import GaloisForLFunctions.RHTower.JointReadingNoGo
import GaloisForLFunctions.RHTower.LandauShadowNoGo
import GaloisForLFunctions.RHTower.SigmaDivisorExhaustion
import GaloisForLFunctions.RHTower.WeightMismatchRefutation

/-!
# Positive formulations extracted from the RHTower no-go theorems

The no-go modules rule out several tempting detectors: Landau positivity is a
real-axis shadow, the pinned joint symmetry has exponent two, and finite
prime-local sources do not provide divisor atoms in the strip.  This module
records the positive mathematical content left by those failures.

The point is not to replace the no-go results.  It packages them as reusable
positive statements:

* parity shadows select the fixed locus of their involution;
* the RH axis is the functional-equation line reflection, not conjugation;
* an odd strip zero activates a concrete finite Euler-Maclaurin certificate;
* pinned prime-local sigma sources are exhausted, so divisor content must be
  global/seam-level rather than finite-prime-local.
-/

noncomputable section

namespace RHTower

open Complex Finset Polynomial Metric Set

/-! ### Generic fixed-locus parity -/

/-- **Fixed-locus parity for any finite involution.**  If a finite weighted
configuration is preserved by an involution, then the parity of the total
weight is the parity of the weight on the fixed locus.  Every free two-point
orbit contributes twice and disappears modulo two.

This is the abstract form shared by the conjugation shadow and the
critical-line reflection shadow. -/
theorem involution_fixed_locus_parity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (σf : ι → ι)
    (hσmem : ∀ i ∈ s, σf i ∈ s)
    (hσm : ∀ i ∈ s, m (σf i) = m i)
    (hσinv : ∀ i ∈ s, σf (σf i) = i) :
    ((-1 : ℂ)) ^ (∑ i ∈ s, m i)
      = (-1) ^ (∑ i ∈ s.filter (fun i => σf i = i), m i) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => σf i = i) m]
  have heven : Even (∑ i ∈ s.filter (fun i => ¬σf i = i), m i) := by
    rw [even_iff_two_dvd,
      ← ZMod.natCast_eq_zero_iff (∑ i ∈ s.filter (fun i => ¬σf i = i), m i) 2]
    push_cast
    refine Finset.sum_involution (fun i _ => σf i) ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨his, -⟩ := Finset.mem_filter.mp hi
      show (m i : ZMod 2) + (m (σf i) : ZMod 2) = 0
      rw [hσm i his]
      exact CharTwo.add_self_eq_zero _
    · intro i hi _ hfix
      exact (Finset.mem_filter.mp hi).2 hfix
    · intro i hi
      obtain ⟨his, hnot⟩ := Finset.mem_filter.mp hi
      show σf i ∈ s.filter (fun i => ¬σf i = i)
      rw [Finset.mem_filter]
      refine ⟨hσmem i his, ?_⟩
      intro hfix
      apply hnot
      calc
        σf i = σf (σf i) := hfix.symm
        _ = i := hσinv i his
    · intro i hi
      exact hσinv i (Finset.mem_filter.mp hi).1
  rw [pow_add, heven.neg_one_pow, mul_one]

/-! ### Axis selection: Landau sees the real axis; FE sees the critical line -/

/-- **Landau's positive content:** the conjugation/Landau shadow selects exactly
the real-axis part of a conjugation-equivariant configuration. -/
theorem landau_shadow_selects_real_axis {ι : Type*}
    (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) (σf : ι → ι)
    (hσmem : ∀ i ∈ s, σf i ∈ s)
    (hσρ : ∀ i ∈ s, ρc (σf i) = (starRingEnd ℂ) (ρc i))
    (hσm : ∀ i ∈ s, m (σf i) = m i)
    (hσinv : ∀ i ∈ s, σf (σf i) = i) :
    ((-1 : ℂ)) ^ (∑ i ∈ s, m i)
      = (-1) ^ (∑ i ∈ s.filter (fun i => (ρc i).im = 0), m i) :=
  conj_equivariant_parity s ρc m σf hσmem hσρ hσm hσinv

/-- **The RH-axis positive content:** the functional-equation line-reflection
shadow selects exactly the critical-line part of a reflection-equivariant
configuration. -/
theorem fe_shadow_selects_critical_line {ι : Type*}
    (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) (σf : ι → ι)
    (hσmem : ∀ i ∈ s, σf i ∈ s)
    (hσρ : ∀ i ∈ s, ρc (σf i) = lineReflection (1 / 2) (ρc i))
    (hσm : ∀ i ∈ s, m (σf i) = m i)
    (hσinv : ∀ i ∈ s, σf (σf i) = i) :
    ((-1 : ℂ)) ^ (∑ i ∈ s, m i)
      = (-1) ^ (∑ i ∈ s.filter (fun i => (ρc i).re = 1 / 2), m i) :=
  neg_one_pow_sum_reflection_equivariant s ρc m σf hσmem hσρ hσm hσinv

/-- **Axis separation, stated positively.**  For one finite configuration
carrying both involutions and no real-axis points, Landau's shadow is trivial
while the FE shadow is the critical-line count. -/
theorem landau_fe_axis_separation {ι : Type*}
    (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) (σc σℓ : ι → ι)
    (hσcmem : ∀ i ∈ s, σc i ∈ s)
    (hσcρ : ∀ i ∈ s, ρc (σc i) = (starRingEnd ℂ) (ρc i))
    (hσcm : ∀ i ∈ s, m (σc i) = m i)
    (hσcinv : ∀ i ∈ s, σc (σc i) = i)
    (hσℓmem : ∀ i ∈ s, σℓ i ∈ s)
    (hσℓρ : ∀ i ∈ s, ρc (σℓ i) = lineReflection (1 / 2) (ρc i))
    (hσℓm : ∀ i ∈ s, m (σℓ i) = m i)
    (hσℓinv : ∀ i ∈ s, σℓ (σℓ i) = i)
    (hoff : ∀ i ∈ s, (ρc i).im ≠ 0) :
    (((-1 : ℂ)) ^ (∑ i ∈ s, m i) = 1) ∧
      (((-1 : ℂ)) ^ (∑ i ∈ s, m i)
        = (-1) ^ (∑ i ∈ s.filter (fun i => (ρc i).re = 1 / 2), m i)) :=
  landau_conj_shadow_vs_fe_line_shadow s ρc m σc σℓ
    hσcmem hσcρ hσcm hσcinv hσℓmem hσℓρ hσℓm hσℓinv hoff

/-- For ξ itself, the Landau/conjugation shadow is trivial on any finite
conjugation-closed off-real zero configuration. -/
theorem xi_landau_shadow_trivial_on_off_real_closed_set (s : Finset ℂ)
    (hclosed : ∀ ρ ∈ s, (starRingEnd ℂ) ρ ∈ s)
    (hoff : ∀ ρ ∈ s, ρ.im ≠ 0) :
    ((-1 : ℂ)) ^ (∑ ρ ∈ s, (analyticOrderAt xi ρ).toNat) = 1 :=
  xi_conj_shadow_blind s hclosed hoff

/-- The same ξ Landau/conjugation shadow as an aggregate even-order statement:
off-real conjugate pairs contribute an even total order. -/
theorem xi_landau_order_sum_even_on_off_real_closed_set (s : Finset ℂ)
    (hclosed : ∀ ρ ∈ s, (starRingEnd ℂ) ρ ∈ s)
    (hoff : ∀ ρ ∈ s, ρ.im ≠ 0) :
    Even (∑ ρ ∈ s, (analyticOrderAt xi ρ).toNat) :=
  xi_conj_order_sum_even s hclosed hoff

/-- The fixed locus of the FE line reflection is exactly the critical line. -/
theorem lineReflection_half_fixed_iff (ρ : ℂ) :
    lineReflection (1 / 2) ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    rw [lineReflection_re] at hre
    norm_num at hre
    linarith
  · intro h
    exact lineReflection_eq_self h

/-! ### Joint symmetry: the positive structure left by the no-go -/

/-- The pinned `{σ_p} × ∂_s` divisor symmetry is a two-torsion symmetry:
every element squares to the identity. -/
theorem pinned_joint_symmetry_two_torsion (g : Equiv.Perm ℂ) (hg : g ∈ jointSym) :
    g ^ 2 = 1 :=
  jointSym_sq g hg

/-- Equivalently, every pinned joint symmetry has order at most two. -/
theorem pinned_joint_symmetry_order_bounded (g : Equiv.Perm ℂ) (hg : g ∈ jointSym) :
    orderOf g ≤ 2 :=
  jointSym_orderOf_le_two g hg

/-- The pinned joint symmetry still acts on the ξ-divisor: the FE generator,
the conjugation generator, and their critical-line composite all preserve
vanishing order. -/
theorem pinned_joint_symmetry_preserves_three_divisor_readings (z : ℂ) :
    analyticOrderAt xi (feEquiv z) = analyticOrderAt xi z ∧
      analyticOrderAt xi (cjEquiv z) = analyticOrderAt xi z ∧
      analyticOrderAt xi ((feEquiv * cjEquiv) z) = analyticOrderAt xi z :=
  ⟨jointSym_feEquiv_order_invariant z,
    jointSym_cjEquiv_order_invariant z,
    jointSym_feEquiv_cjEquiv_order_invariant z⟩

/-! ### RH ladder reading left by the parity no-go -/

/-- The first RH ladder rung is exactly the positive even-order requirement on
right-half ξ-zeros.  This is the useful rung statement left after single-orbit
parity invariants are refuted. -/
theorem rh_ladder_one_even_order_positive :
    RHLadder 1 ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → Even (analyticOrderAt xi ρ).toNat :=
  rhLadder_one_iff_even_order

/-! ### Odd zeros: the no-go activates a finite positive certificate -/

/-- **Odd strip zeros activate finite data.**  If a strip point has odd
ξ-order, then a completed Euler-Maclaurin carrier supplies an isolating
annulus, a circle trace, and universal periodic-probe annihilation. -/
theorem odd_strip_zero_activates_em_certificate {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m) (hodd : Odd m) :
    ∃ (r₀ r R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < r ∧ r < R ∧ 1 ≤ N ∧
      (∀ z ∈ ball ρ R \ closedBall ρ r₀, completedEM N z ≠ 0) ∧
      (∃ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
        ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ 2 = completedEM N (circleMap ρ r θ)) ∧
      ∀ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ 2 = completedEM N (circleMap ρ r θ)) →
        V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
        ∀ p : ℝ → ℂ,
          ContinuousOn p
            (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
          (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
            p (θ + 2 * Real.pi) = p θ) →
          ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
            doubledTrace (-1) V θ * p θ = 0 :=
  carrier_mass_zero_at_odd_xi_order h0 h1 hm hodd

/-- **Odd strip zeros have mirror-paired finite certificates.**  The same
finite certificate fires at the zero and at its critical-line reflection. -/
theorem odd_strip_zero_activates_mirror_em_certificates {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m) (hodd : Odd m) :
    (∃ (r₀ r R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < r ∧ r < R ∧ 1 ≤ N ∧
      (∀ z ∈ ball ρ R \ closedBall ρ r₀, completedEM N z ≠ 0) ∧
      (∃ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
        ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ 2 = completedEM N (circleMap ρ r θ)) ∧
      ∀ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ 2 = completedEM N (circleMap ρ r θ)) →
        V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
        ∀ p : ℝ → ℂ,
          ContinuousOn p
            (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
          (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
            p (θ + 2 * Real.pi) = p θ) →
          ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
            doubledTrace (-1) V θ * p θ = 0) ∧
    (∃ (r₀ r R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < r ∧ r < R ∧ 1 ≤ N ∧
      (∀ z ∈ ball (lineReflection (1 / 2) ρ) R
          \ closedBall (lineReflection (1 / 2) ρ) r₀,
        completedEM N z ≠ 0) ∧
      (∃ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
        ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ 2 = completedEM N
            (circleMap (lineReflection (1 / 2) ρ) r θ)) ∧
      ∀ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ 2 = completedEM N
            (circleMap (lineReflection (1 / 2) ρ) r θ)) →
        V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
        ∀ p : ℝ → ℂ,
          ContinuousOn p
            (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
          (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
            p (θ + 2 * Real.pi) = p θ) →
          ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
            doubledTrace (-1) V θ * p θ = 0) :=
  carrier_mass_zero_mirror_pair_at_odd_xi_order h0 h1 hm hodd

/-- **Odd strip zero = finite certificate plus prime invisibility.**  At an
odd ξ-zero in the strip, every finite Euler atlas is a unit at the point while
the Euler-Maclaurin carrier certificate is activated. -/
theorem odd_strip_zero_certificate_and_prime_invisibility {ρ : ℂ}
    (hz : xi ρ = 0)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m) (hodd : Odd m)
    {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    analyticOrderAt (eulerPartial P) ρ = 0 ∧
      analyticOrderAt xi ρ ≠ 0 ∧
      ∃ (r₀ r R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < r ∧ r < R ∧ 1 ≤ N ∧
        (∀ z ∈ ball ρ R \ closedBall ρ r₀, completedEM N z ≠ 0) ∧
        (∃ V : ℝ → ℂ,
          ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
          ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
            V θ ^ 2 = completedEM N (circleMap ρ r θ)) ∧
        ∀ V : ℝ → ℂ,
          ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) →
          (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
            V θ ^ 2 = completedEM N (circleMap ρ r θ)) →
          V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
          ∀ p : ℝ → ℂ,
            ContinuousOn p
              (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
            (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
              p (θ + 2 * Real.pi) = p θ) →
            ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
              doubledTrace (-1) V θ * p θ = 0 := by
  have h0 : 0 < ρ.re := xi_zero_re_pos hz
  have h1 : ρ.re < 1 := xi_zero_re_lt_one hz
  exact ⟨eulerPartial_orderAt_zero hP h0,
    xi_zero_order_ne_zero hz,
    carrier_mass_zero_at_odd_xi_order h0 h1 hm hodd⟩

/-! ### Pinned sigma source exhaustion, positively packaged -/

/-- **Pinned prime-local sigma source exhaustion.**  At a strip zero, the
currently available pinned `{σ_p}` source channels contribute no local divisor
atoms: prime-local source maps are zero, finite Euler atlases are units, the
ξ-order is nonzero, and multiplicative sigma jets vanish in the local
divisor-jet quotient. -/
theorem pinned_sigma_sources_exhausted_positive {R Sigma : Type*} [CommRing R] (m : ℕ)
    (u : Polynomial R) (hjet : Sigma → Polynomial R)
    {ρ : ℂ} (hz : xi ρ = 0)
    {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {A : ℕ → ℕ} (hA : SigmaSourceMap A ρ) :
    (∀ p, 2 ≤ p → A p = 0) ∧
      analyticOrderAt (eulerPartial P) ρ = 0 ∧
      analyticOrderAt xi ρ ≠ 0 ∧
      ¬ HasNontrivialSigmaJet m
        (fun p => (((Polynomial.X : Polynomial R) ^ m) * u) * hjet p) :=
  pinnedSigmaDivisorSources_killed m u hjet hz hP hA

/-- **Additive carrier versus multiplicative source, positive mismatch.**  If
an Euler-Maclaurin split is present at a strip ξ-zero, the additive carrier
sees at least one local zero atom while every pinned prime-local source map
and multiplicative sigma jet remains zero. -/
theorem additive_carrier_multiplicative_source_mismatch_positive
    {R Sigma : Type*} [CommRing R] (m : ℕ)
    (u0 : Polynomial R) (hjet : Sigma → Polynomial R)
    {ρ : ℂ} (hz : xi ρ = 0)
    {A : ℕ → ℕ} (hA : SigmaSourceMap A ρ)
    {r₀ R₀ : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (hdata : EMSplitData ρ r₀ R₀ N zs u) :
    (∀ p, 2 ≤ p → A p = 0) ∧
      1 ≤ zs.length ∧
      ¬ HasNontrivialSigmaJet m
        (fun p => (((Polynomial.X : Polynomial R) ^ m) * u0) * hjet p) :=
  pinnedSigmaDivisorSources_mismatch_with_emSplit m u0 hjet hz hA hdata

end RHTower
