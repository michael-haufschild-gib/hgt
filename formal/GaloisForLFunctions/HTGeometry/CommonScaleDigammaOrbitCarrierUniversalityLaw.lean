import GaloisForLFunctions.HTGeometry.DigammaOrbitCarrier
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance

/-!
# Common-scale digamma orbit-carrier universality law

The unit-scale arbitrary-orbit theorem and the arbitrary-scale single-factor theorem are two faces
of one law.  Translation and unconditional argument scaling give a finite charged digamma orbit at
every nonzero common complex scale and every base shift.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions

/-- **Common-scale digamma orbit-carrier universality law.**  A finite affine common-scale digamma
orbit is hypertranscendental exactly on the nonneutral side needed here: nonzero total charge and
nonzero common scale force hypertranscendence for every base shift. -/
theorem hypertranscendental_commonScale_digamma_orbit_charge
    {r : ℕ} (m : Fin r → ℂ) (nn : Fin r → ℕ)
    {c : ℂ} (hc : c ≠ 0) (d : ℂ) (hM : ∑ k, m k ≠ 0) :
    Hypertranscendental
      (fun s => ∑ k, m k * Complex.digamma (c * s + d + (nn k : ℂ))) := by
  let F : ℂ → ℂ := fun w => ∑ k, m k * Complex.digamma (w + (nn k : ℂ))
  have htranslate : Hypertranscendental (fun w => F (w + d)) :=
    (hypertranscendental_comp_add_const_iff (f := F) d).mpr
      (by simpa only [F] using hypertranscendental_digamma_orbit_charge m nn hM)
  have hscale :=
    (hypertranscendental_comp_const_mul_iff_uncond
      (f := fun w => F (w + d)) hc).mpr htranslate
  simpa only [F, add_assoc] using hscale

/-- **All-order affine orbit-jet decomposition.**  Pulling a finite integer-shift digamma orbit
back along `s ↦ c * s + d` multiplies its order-`j` jet by `c ^ j`.  Off the pole orbit, that jet
then splits exactly into total charge times the single common digamma jet plus a rational tail. -/
theorem commonScale_digamma_orbit_jet_decomposition
    {r : ℕ} (m : Fin r → ℂ) (nn : Fin r → ℕ)
    (c d : ℂ) (j : ℕ) (s : ℂ)
    (hoff : ∀ p : ℕ, c * s + d ≠ -(p : ℂ)) :
    iteratedDeriv j
        (fun z => ∑ k, m k * Complex.digamma (c * z + d + (nn k : ℂ))) s =
      c ^ j *
        ((∑ k, m k) * iteratedDeriv j Complex.digamma (c * s + d) +
          ∑ k, m k * ∑ i ∈ Finset.range (nn k),
            (-1) ^ j * (j.factorial : ℂ) / (c * s + d + i) ^ (j + 1)) := by
  let F : ℂ → ℂ := fun w => ∑ k, m k * Complex.digamma (w + (nn k : ℂ))
  have hchain := iteratedDeriv_comp_mul_left_uncond (fun w => F (w + d)) c j s
  rw [congrFun (iteratedDeriv_comp_add_const j F d) (c * s)] at hchain
  have hcont : ∀ k : Fin r,
      ContDiffAt ℂ (j : ℕ) (fun w => Complex.digamma (w + (nn k : ℂ))) (c * s + d) := by
    intro k
    have hshift : ∀ p : ℕ, c * s + d + (nn k : ℂ) ≠ -(p : ℂ) := by
      intro p hp
      refine hoff (p + nn k) ?_
      push_cast at hp ⊢
      linear_combination hp
    exact (contDiffAt_digamma_n
      (c * s + d + (nn k : ℂ)) hshift j).comp (c * s + d)
        (contDiffAt_id.add contDiffAt_const)
  have hsum : iteratedDeriv j F (c * s + d) =
      ∑ k, m k * iteratedDeriv j Complex.digamma (c * s + d + (nn k : ℂ)) := by
    rw [show F = ∑ k, (fun w => m k * Complex.digamma (w + (nn k : ℂ))) from by
      funext w
      simp only [F, Finset.sum_apply]]
    rw [iteratedDeriv_sum (fun k _ => contDiffAt_const.mul (hcont k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [iteratedDeriv_const_mul (m k) (hcont k)]
    congr 1
    rw [show (fun w => Complex.digamma (w + (nn k : ℂ))) =
        (fun w => Complex.digamma ((nn k : ℂ) + w)) from by
          funext w
          rw [add_comm]]
    simp only [iteratedDeriv_comp_const_add]
    rw [add_comm (nn k : ℂ) (c * s + d)]
  rw [hchain, hsum, HTGeometry.iteratedDeriv_digamma_charge_general
    (c * s + d) hoff nn m j]

/-- **Neutral all-order affine orbit collapse.**  Zero total charge removes the common digamma
carrier at every derivative order, leaving only the scaled rational shift tail. -/
theorem commonScale_digamma_orbit_neutral_jet_collapse
    {r : ℕ} (m : Fin r → ℂ) (nn : Fin r → ℕ)
    (c d : ℂ) (hcharge : ∑ k, m k = 0) (j : ℕ) (s : ℂ)
    (hoff : ∀ p : ℕ, c * s + d ≠ -(p : ℂ)) :
    iteratedDeriv j
        (fun z => ∑ k, m k * Complex.digamma (c * z + d + (nn k : ℂ))) s =
      c ^ j * ∑ k, m k * ∑ i ∈ Finset.range (nn k),
        (-1) ^ j * (j.factorial : ℂ) / (c * s + d + i) ^ (j + 1) := by
  rw [commonScale_digamma_orbit_jet_decomposition m nn c d j s hoff, hcharge,
    zero_mul, zero_add]

/-- **Sharp common-scale digamma orbit phase law.**  At arbitrary affine common scale, nonzero
total charge gives global hypertranscendence, while zero total charge cancels the digamma carrier
and leaves the exact rational shift tail at every point off the Gamma pole orbit.  The all-order
version of the neutral branch is `commonScale_digamma_orbit_neutral_jet_collapse`. -/
theorem commonScale_digamma_orbit_charge_phase
    {r : ℕ} (m : Fin r → ℂ) (nn : Fin r → ℕ)
    {c : ℂ} (hc : c ≠ 0) (d : ℂ) :
    ((∑ k, m k ≠ 0) →
      Hypertranscendental
        (fun s => ∑ k, m k * Complex.digamma (c * s + d + (nn k : ℂ)))) ∧
    ((∑ k, m k = 0) → ∀ s : ℂ,
      (∀ p : ℕ, c * s + d ≠ -(p : ℂ)) →
      (∑ k, m k * Complex.digamma (c * s + d + (nn k : ℂ))) =
        ∑ k, m k * ∑ i ∈ Finset.range (nn k), (c * s + d + (i : ℂ))⁻¹) := by
  refine ⟨hypertranscendental_commonScale_digamma_orbit_charge m nn hc d, ?_⟩
  intro hcharge s hoff
  have hcollapse := HTGeometry.iteratedDeriv_digamma_charge_collapse
    (c * s + d) hoff nn m 0 hcharge
  simpa only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    one_mul, zero_add, pow_one, one_div, add_assoc] using hcollapse

end GaloisForLFunctions

end
