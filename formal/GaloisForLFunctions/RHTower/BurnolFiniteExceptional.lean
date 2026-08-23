import GaloisForLFunctions.RHTower.BurnolResidueShape
import GaloisForLFunctions.RHTower.MellinRealDecay
import GaloisForLFunctions.RHTower.MultiplierRealBound
import GaloisForLFunctions.HTGeometry.PrincipalPartPolynomial

/-!
# Finitely many exceptional zeros

If the Mellin transform of a vector of the dense subspace is divisible by `ζ` at every nontrivial
zero *outside a finite set `R`*, Theorem 5.2 collapses to a finite sum, and — by the shape of the
residues — expresses the transform as `ζ(Z)` times a *rational* function whose poles lie in `R`:

`M(f)(Z) = ζ(Z)·(sum of the principal parts of M(f)/ζ at the points of R)(Z)`.

## Main results

* `extendedMellin_eq_zeta_mul_principalSum`
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

/-- Residues vanish at every nontrivial zero where `ζ` divides the transform. -/
theorem laurentCoeff_burnolIntegrand_eq_zero_of_dvd (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {Z ρ : ℂ} (hZζ : riemannZeta Z ≠ 0) (hzero : riemannZeta ρ = 0)
    (hdvd : meromorphicOrderAt riemannZeta ρ
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) ρ) :
    laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1) = 0 := by
  have hρZ : ρ ≠ Z := by
    intro hcon
    rw [hcon] at hzero
    exact hZζ hzero
  have hmero : MeromorphicAt (extendedMellinContinuation a c d f) ρ :=
    meromorphicAt_extendedMellinContinuation ha hev hc hd ρ
  refine laurentCoeff_burnolIntegrand_eq_zero_of_le hmero ?_
  rw [meromorphicOrderAt_burnolIntegrand hmero hZζ hρZ]
  induction hx : meromorphicOrderAt riemannZeta ρ with
  | top =>
      rw [hx] at hdvd
      have htop' : meromorphicOrderAt (extendedMellinContinuation a c d f) ρ = ⊤ :=
        top_le_iff.1 hdvd
      rw [htop']
      simp
  | coe n =>
      rw [hx] at hdvd
      exact withTop_sub_nonneg_of_le hdvd

/-- **The residue series collapses to the finitely many exceptional zeros.** -/
theorem extendedMellin_eq_zeta_mul_principalSum (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {R : Finset ℂ}
    (hRzero : ∀ ρ ∈ R, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ∉ R →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) ρ)
    {k : ℕ}
    (hk : ∀ ρ ∈ R, AnalyticAt ℂ
      (laurentShift (burnolQuotient (extendedMellinContinuation a c d f)) ρ k) 0)
    {Z : ℂ} (hZζ : riemannZeta Z ≠ 0) (hZ1 : Z ≠ 1) (hZ0 : Z ≠ 0) :
    extendedMellinContinuation a c d f Z
      = riemannZeta Z
        * principalSum (burnolQuotient (extendedMellinContinuation a c d f)) R k Z := by
  classical
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨T, hmono, htop, hT1, hconv⟩ :=
    exists_seq_tendsto_residueSum_extendedMellin ha hev hc hd hrapid
  have hlim := hconv Z hZζ hZ1 hZ0
  -- the sum collapses to `R`
  have hRsub : ∀ᶠ n : ℕ in atTop, R ⊆ nontrivialZeroFinset (T n) := by
    have hbound : ∃ M : ℝ, ∀ ρ ∈ R, |ρ.im| < M := by
      rcases R.eq_empty_or_nonempty with rfl | hne
      · exact ⟨1, by simp⟩
      · refine ⟨(R.sup' hne fun ρ => |ρ.im|) + 1, fun ρ hρ => ?_⟩
        have := Finset.le_sup' (f := fun ρ : ℂ => |ρ.im|) hρ
        linarith
    obtain ⟨M, hM⟩ := hbound
    filter_upwards [htop.eventually_ge_atTop M] with n hn
    intro ρ hρ
    obtain ⟨hzero, h1, h2⟩ := hRzero ρ hρ
    exact mem_nontrivialZeroFinset.2 ⟨hzero, h1, h2, lt_of_lt_of_le (hM ρ hρ) hn⟩
  have heq : ∀ᶠ n : ℕ in atTop,
      (∑ ρ ∈ nontrivialZeroFinset (T n),
        laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1))
        = ∑ ρ ∈ R,
          laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1) := by
    filter_upwards [hRsub] with n hn
    refine (Finset.sum_subset hn ?_).symm
    intro ρ hρ hρR
    obtain ⟨hzero, h1, h2, -⟩ := mem_nontrivialZeroFinset.1 hρ
    exact laurentCoeff_burnolIntegrand_eq_zero_of_dvd ha0 hev hc hd hZζ hzero
      (hdvd ρ hzero h1 h2 hρR)
  have hconst : Tendsto (fun _ : ℕ =>
      ∑ ρ ∈ R, laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1))
      atTop (𝓝 (extendedMellinContinuation a c d f Z)) := hlim.congr' heq
  have hval := tendsto_nhds_unique tendsto_const_nhds hconst
  rw [← hval, principalSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  obtain ⟨hzero, -, -⟩ := hRzero ρ hρ
  have hZρ : Z ≠ ρ := by
    intro hcon
    rw [hcon] at hZζ
    exact hZζ hzero
  exact laurentCoeff_burnolIntegrand_eq_zeta_mul_principalPart hZρ (hk ρ hρ)

end

end RHTower
