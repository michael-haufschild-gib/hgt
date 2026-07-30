import GaloisForLFunctions.HTGeometry.NevanlinnaJetTriangular

/-!
# Local Nevanlinna jet triangularity

The projective Nevanlinna coordinates are meromorphic globally and smooth only off their polar
divisor.  The original triangular jet theorem was stated for globally smooth inputs.  This module
proves the intrinsic local version on an arbitrary open regular locus, which is the form needed by
actual Nevanlinna matrices.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Topology
open scoped BigOperators

noncomputable section

/-- Recursive Nevanlinna jet coefficients remain smooth on every open locus on which the two
input functions are smooth. -/
theorem contDiffOn_nevanlinnaJetCoeff
    {a q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : ContDiffOn ℂ ⊤ a U) (hq : ContDiffOn ℂ ⊤ q U) :
    ∀ r k, ContDiffOn ℂ ⊤ (nevanlinnaJetCoeff a q r k) U := by
  intro r
  induction r with
  | zero =>
      intro k
      simp only [nevanlinnaJetCoeff]
      split
      · exact ha
      · exact contDiffOn_const
  | succ r ih =>
      intro k
      simp only [nevanlinnaJetCoeff]
      apply ContDiffOn.add
      · simpa using (ih k).deriv_of_isOpen hU (by simp)
      · split
        · exact contDiffOn_const
        · exact (contDiffOn_const.mul
            (by simpa using hq.deriv_of_isOpen hU (by simp))).mul (ih (k - 1))

/-- Differentiating the order-`r` expansion is valid on an open regular locus; no global
smoothness across the polar divisor is required. -/
theorem hasDerivAt_nevanlinnaJetExpansion_of_contDiffOn
    {a q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : ContDiffOn ℂ ⊤ a U) (hq : ContDiffOn ℂ ⊤ q U)
    (tau z : ℂ) (hz : z ∈ U) (hden : tau - q z ≠ 0) (r : ℕ) :
    HasDerivAt (nevanlinnaJetExpansion a q tau r)
      (nevanlinnaJetExpansion a q tau (r + 1) z) z := by
  have hznhds : U ∈ 𝓝 z := hU.mem_nhds hz
  have hqderiv : HasDerivAt q (deriv q z) z :=
    (hq.contDiffAt hznhds).differentiableAt (by simp) |>.hasDerivAt
  have hterm : ∀ k ∈ Finset.range (r + 1),
      HasDerivAt
        (fun w => nevanlinnaJetCoeff a q r k w *
          ((tau - q w)⁻¹) ^ (k + 1))
        (deriv (nevanlinnaJetCoeff a q r k) z * ((tau - q z)⁻¹) ^ (k + 1) +
          nevanlinnaJetCoeff a q r k z *
            ((k + 1 : ℕ) : ℂ) * deriv q z * ((tau - q z)⁻¹) ^ (k + 2)) z := by
    intro k _hk
    have hb : HasDerivAt (nevanlinnaJetCoeff a q r k)
        (deriv (nevanlinnaJetCoeff a q r k) z) z :=
      ((contDiffOn_nevanlinnaJetCoeff hU ha hq r k).contDiffAt hznhds).differentiableAt
        (by simp) |>.hasDerivAt
    have hp := hasDerivAt_nevanlinnaCauchyPower hqderiv hden k
    convert! hb.mul hp using 1
    all_goals ring
  have hsum := HasDerivAt.fun_sum hterm
  have hzero : deriv (nevanlinnaJetCoeff a q r (r + 1)) z = 0 := by
    rw [nevanlinnaJetCoeff_eq_zero_of_lt a q (Nat.lt_succ_self r), deriv_zero]
    rfl
  have hstep := nevanlinnaJet_sum_step r
    (fun k => deriv (nevanlinnaJetCoeff a q r k) z)
    (fun k => nevanlinnaJetCoeff a q r k z)
    (fun k => ((tau - q z)⁻¹) ^ (k + 1)) (deriv q z) hzero
  apply hsum.congr_deriv
  rw [hstep]
  simp only [nevanlinnaJetExpansion, nevanlinnaJetCoeff]

/-- **Local genuine-jet expansion.**  On an open regular locus, every iterated derivative of
`a/(tau-q)` is its finite triangular Cauchy-power expansion. -/
theorem iteratedDeriv_nevanlinnaKernel_eq_expansion_of_contDiffOn
    {a q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : ContDiffOn ℂ ⊤ a U) (hq : ContDiffOn ℂ ⊤ q U)
    (tau z : ℂ) (hz : z ∈ U) (hden : tau - q z ≠ 0) : ∀ r,
    iteratedDeriv r (fun w => a w * (tau - q w)⁻¹) z =
      nevanlinnaJetExpansion a q tau r z := by
  intro r
  induction r generalizing z with
  | zero =>
      simp [nevanlinnaJetExpansion, nevanlinnaJetCoeff]
  | succ r ih =>
      rw [iteratedDeriv_succ]
      have hqcont : ContinuousAt q z := (hq.contDiffAt (hU.mem_nhds hz)).continuousAt
      have hdenEv : ∀ᶠ w in 𝓝 z, tau - q w ≠ 0 :=
        ((continuousAt_const.sub hqcont).eventually_ne hden)
      have hlocal :
          iteratedDeriv r (fun w => a w * (tau - q w)⁻¹) =ᶠ[𝓝 z]
            nevanlinnaJetExpansion a q tau r := by
        filter_upwards [hdenEv, hU.mem_nhds hz] with w hwden hwU
        exact ih w hwU hwden
      rw [hlocal.deriv_eq]
      exact (hasDerivAt_nevanlinnaJetExpansion_of_contDiffOn
        hU ha hq tau z hz hden r).deriv

end

end GaloisForLFunctions.HTGeometry
