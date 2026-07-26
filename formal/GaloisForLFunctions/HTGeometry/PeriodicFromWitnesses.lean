import GaloisForLFunctions.HTGeometry.GeometricPeriodicLeastLevel
import GaloisForLFunctions.HTGeometry.GeometricPeriodicEveryLevel

/-!
# Realizations of the tail-periodicity interface

Tail periodicity with an explicit starting index is realized by the residue extension of an
arbitrary phase sequence: `n ↦ v (n % p)` is periodic from index `0` for every `p`, and it is
unimodular whenever `v` is.  Constants, the degenerate period `0`, later starting indices, and
pointwise sums and products all stay inside the interface.

Substituting the residue extension removes the periodicity premise from the geometric level
exactness theorems: their conclusion holds for the phase family of *every* sequence read modulo the
period.
-/

namespace GaloisForLFunctions

open Filter Finset MvPolynomial Polynomial PowerSeries Topology

noncomputable section

/-! ## Realizations -/

theorem periodicFrom_const (c : ℂ) (p T : ℕ) : PeriodicFrom (fun _ => c) p T :=
  fun _ _ => rfl

/-- The degenerate period is satisfied by every sequence. -/
theorem periodicFrom_period_zero (u : ℕ → ℂ) (T : ℕ) : PeriodicFrom u 0 T := by
  intro n _
  rw [Nat.add_zero]

/-- Tail periodicity survives moving the starting index later. -/
theorem PeriodicFrom.mono_start {u : ℕ → ℂ} {p T T' : ℕ}
    (h : PeriodicFrom u p T) (hT : T ≤ T') : PeriodicFrom u p T' :=
  fun n hn => h n (le_trans hT hn)

/-- **Residue extension.**  Reading any sequence modulo a period produces a sequence that is
periodic from the very first index. -/
theorem periodicFrom_mod (v : ℕ → ℂ) (p : ℕ) :
    PeriodicFrom (fun n => v (n % p)) p 0 := by
  intro n _
  simp [Nat.add_mod_right]

theorem norm_mod_eq_one {v : ℕ → ℂ} (hv : ∀ n, ‖v n‖ = 1) {p : ℕ} (n : ℕ) :
    ‖(fun m => v (m % p)) n‖ = 1 := hv (n % p)

theorem PeriodicFrom.add {u w : ℕ → ℂ} {p T : ℕ}
    (hu : PeriodicFrom u p T) (hw : PeriodicFrom w p T) :
    PeriodicFrom (fun n => u n + w n) p T := by
  intro n hn
  simp only
  rw [hu n hn, hw n hn]

theorem PeriodicFrom.mul {u w : ℕ → ℂ} {p T : ℕ}
    (hu : PeriodicFrom u p T) (hw : PeriodicFrom w p T) :
    PeriodicFrom (fun n => u n * w n) p T := by
  intro n hn
  simp only
  rw [hu n hn, hw n hn]

theorem PeriodicFrom.const_smul {u : ℕ → ℂ} {p T : ℕ} (c : ℂ)
    (hu : PeriodicFrom u p T) : PeriodicFrom (fun n => c * u n) p T := by
  intro n hn
  simp only
  rw [hu n hn]

/-! ## The interface disappears from the level exactness theorems -/

/-- **Least-level exactness for every residue phase family.**  The tail-periodicity premise of the
least grouped level polynomial theorem is met by the residue extension of an arbitrary unimodular
sequence. -/
theorem exists_periodicGeometric_leastLevelPolynomial_eq_zero_of_mod
    {F : PowerSeries ℂ} {v : ℕ → ℂ}
    {A lam c : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hbpos : ∀ i, 0 < A * lam ^ i + c)
    {period : ℕ} (hperiod : 0 < period)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(A * lam ^ i + c)) : ℝ) : ℂ) * v (i % period))
    (hvNorm : ∀ i, ‖v i‖ = 1)
    {n D K₀ τ M₀ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hw₀ : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0) :
    ∃ K M q₀ : ℕ,
      let S := polynomialPatternSurvivors n D K τ Q M
      let Face := geometricPatternFace lam S
      S.Nonempty ∧ q₀ ≥ K ∧
        periodicGeometricLevelPolynomial n D K τ Q q₀ period Face
            (fun i => v (i % period)) c lam
            (geometricPatternMinimum lam S) = 0 :=
  exists_periodicGeometric_leastLevelPolynomial_eq_zero hA hlam hbpos hcoeff
    (fun i => norm_mod_eq_one hvNorm i) hperiod (periodicFrom_mod v period)
    Q hrel hD hDmax p₀ hcount₀ hw₀

/-- **Target-level exactness for every residue phase family.** -/
theorem exists_periodicGeometric_targetLevelPolynomial_eq_zero_of_mod
    {F : PowerSeries ℂ} {v : ℕ → ℂ}
    {A lam c : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hbpos : ∀ i, 0 < A * lam ^ i + c)
    {period : ℕ} (hperiod : 0 < period)
    {sigma : ℕ} (hsigma : sigma < period)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(A * lam ^ i + c)) : ℝ) : ℂ) * v (i % period))
    (hvNorm : ∀ i, ‖v i‖ = 1)
    {n D K₀ τ M₀ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hw₀ : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0) :
    ∃ K M q₀ : ℕ,
      let target := lam ^ (K - K₀) * geometricPatternValue lam p₀
      let S := (polynomialPatternSurvivors n D K τ Q M).filter
        fun p => geometricPatternValue lam p ≤ target
      S.Nonempty ∧
        (S.filter fun p => geometricPatternValue lam p = target).Nonempty ∧
        (S.filter fun p => geometricPatternValue lam p = target).card ≠ 1 ∧
        K ≤ q₀ ∧ q₀ % period = sigma ∧
        periodicGeometricLevelPolynomial n D K τ Q q₀ period S
            (fun i => v (i % period)) c lam target = 0 :=
  exists_periodicGeometric_targetLevelPolynomial_eq_zero hA hlam hbpos hcoeff
    (fun i => norm_mod_eq_one hvNorm i) hperiod hsigma (periodicFrom_mod v period)
    Q hrel hD hDmax p₀ hcount₀ hw₀

end

end GaloisForLFunctions
