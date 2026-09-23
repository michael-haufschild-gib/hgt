import GaloisForLFunctions.RHTower.PrimePolarResidueCancellation

/-!
# The prime--polar RH detection criterion

The capstone `(28)` of `prime-polar-moving-tent-divisor-tomography` §5: the Riemann Hypothesis, read
off the analyticity of the prime--polar observable.

The load-bearing (prime) term of the continuation `Pcal_L` is
`primeObservable L s = -2·I_L(s)·(-ζ'/ζ)(s-½)` with `I_L(s) = A_L(s-1)²`.  By the multiplicity-exact
pole tomography (`offcritical_residue`), each zeta zero `ρ` with `Re ρ > ½` makes this observable have a
genuine simple pole at `s = ρ + ½` (residue `2·m(ρ)·A_L(ρ-½)² ≠ 0`) — so the observable tends to *no*
finite limit there (`primeObservable_no_limit`).  Consequently, regularity of the observable on
`Re s > 1` forecloses every off-critical zero: `RH_of_primeObservable_regular` is the detection direction
of `(28)`, assembled entirely from the proven residue facts.
-/

open Filter Topology

namespace RHTower


/-- The load-bearing (prime) term of the prime–polar observable `Pcal_L`:
`-2·I_L(s)·(-ζ'/ζ)(s-½)` with `I_L(s) = A_L(s-1)²`.  Its poles in `Re s > 1` are exactly the shifted
off-critical zeta zeros. -/
noncomputable def primeObservable (L : ℝ) (s : ℂ) : ℂ :=
  -2 * (rectangularWindowAmplitude L (s - 1)) ^ (2 : ℕ)
    * (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2))

/-- **Off-critical detection.**  A zeta zero `ρ` with `Re ρ > 1/2` makes the observable have a genuine
singularity at `s = ρ + ½`: it tends to no finite limit there. -/
theorem primeObservable_no_limit (L : ℝ) (hL : 0 < L) {ρ : ℂ}
    (hρre : 1 / 2 < ρ.re) (hζρ : riemannZeta ρ = 0) :
    ¬ ∃ M : ℂ, Tendsto (primeObservable L) (𝓝[≠] (ρ + 1 / 2)) (𝓝 M) := by
  rintro ⟨M, hM⟩
  obtain ⟨m, hm1, hres, hne⟩ := offcritical_residue L hL hρre hζρ
  have ha : Tendsto (fun s : ℂ => s - (ρ + 1 / 2)) (𝓝[≠] (ρ + 1 / 2)) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' (ρ + 1 / 2) 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  have h0 := ha.mul hM
  rw [zero_mul] at h0
  exact hne (tendsto_nhds_unique hres h0)

/-- **The prime–polar RH criterion** (§5, eq. 28, detection direction).  If the prime observable has a
finite limit at every point of `Re s > 1` *other than the shifted `ζ`-pole* `s = 3/2`, then the Riemann
zeta function has no zeros with `Re > 1/2`.  The point `s = 3/2` carries `ζ`'s pole (at `s-½ = 1`)
unconditionally — cancelled by the polar renormalization, not the bare observable — while every
off-critical zero gives a genuine singularity at `s = ρ + ½ ≠ 3/2` (`primeObservable_no_limit`), so the
exclusion loses no detection and regularity forecloses those zeros. -/
theorem RH_of_primeObservable_regular (L : ℝ) (hL : 0 < L)
    (hreg : ∀ a : ℂ, 1 < a.re → a ≠ 3 / 2 → ∃ M : ℂ, Tendsto (primeObservable L) (𝓝[≠] a) (𝓝 M)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_zero_re_le_half]
  intro ρ hζρ
  have hρ1 : ρ ≠ 1 := riemannZeta_zero_ne_one hζρ
  by_contra h
  have hgt : 1 / 2 < ρ.re := not_le.mp h
  have hre : 1 < (ρ + 1 / 2).re := by rw [Complex.add_re]; simp; linarith
  have hne32 : ρ + 1 / 2 ≠ 3 / 2 := fun heq => hρ1 (by linear_combination heq)
  exact primeObservable_no_limit L hL hgt hζρ (hreg (ρ + 1 / 2) hre hne32)
