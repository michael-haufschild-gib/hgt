import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerEulerEnvelope

/-!
# The two-atom law of the first open window

In the window `r ∈ (221/400, log 2)` the only shifts an odd test of aperture `r` can see are `2` and
`3`: the square `4` and the product `6` lie past the horizon `2r < 2 log 2 < log 6`, so the cost
side of the ledger there has exactly two atoms, and the only lag available to pay them is the
**ratio** `log(3/2)`, which carries no atom at all.

The three-shift Gram form at `{0, a, b}` gives, for every pair of weights,

    2λ A(a) + 2μ A(b) ≤ (1 + λ² + μ²) A(0) + 2λμ A(b − a),

and optimizing the diagonal weight `λ = μ = θ` gives the sharp two-atom law

    (A(a) + A(b))² ≤ 2 A(0) (A(0) + A(b − a)).

At `a = log 2`, `b = log 3` this says: the joint charge of the two atoms of the first open window is
controlled by the mass together with the charge at the *free* ratio lag `log(3/2)`. Anti-correlation
at that lag strictly reduces what the two primes can demand, and full resonance there is the only
configuration in which the two atoms can reach the trivial ceiling `2 A(0)`. The ratio lag is the
window's single degree of freedom, and the law prices it exactly.
-/

open MeasureTheory
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F : ℝ → ℝ}

/-- **The three-shift Gram law.** For all shifts `a, b` and all weights,

    2λ A(a) + 2μ A(b) ≤ (1 + λ² + μ²) A(0) + 2λμ A(b − a),

the positive semidefiniteness of the incidence matrix at `{0, a, b}` written out. -/
theorem three_shift_gram (hF : Continuous F) (hFc : HasCompactSupport F) (lam mu a b : ℝ) :
    2 * lam * autoCorr F a + 2 * mu * autoCorr F b
      ≤ (1 + lam ^ 2 + mu ^ 2) * autoCorr F 0 + 2 * lam * mu * autoCorr F (b - a) := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have hT : ∀ t : ℝ, ContCompact (fun u => F (u + t)) := fun t => hFn.translate t
  have hX : ContCompact (fun u => F u - lam * F (u + a)) :=
    hFn.sub_nice (ContCompact.const_mul_nice lam (hT a))
  -- the six base pairings
  have q00 : testPairing F F = autoCorr F 0 := testPairing_self_eq_autoCorr_zero F
  have q0a : testPairing F (fun u => F (u + a)) = autoCorr F a := rfl
  have q0b : testPairing F (fun u => F (u + b)) = autoCorr F b := rfl
  have qa0 : testPairing (fun u => F (u + a)) F = autoCorr F a := by
    rw [testPairing_comm]; exact q0a
  have qb0 : testPairing (fun u => F (u + b)) F = autoCorr F b := by
    rw [testPairing_comm]; exact q0b
  have qaa : testPairing (fun u => F (u + a)) (fun u => F (u + a)) = autoCorr F 0 := by
    rw [testPairing_translate F F a]; exact q00
  have qbb : testPairing (fun u => F (u + b)) (fun u => F (u + b)) = autoCorr F 0 := by
    rw [testPairing_translate F F b]; exact q00
  have qab : testPairing (fun u => F (u + a)) (fun u => F (u + b)) = autoCorr F (b - a) :=
    testPairing_translate_pair F a b
  have qba : testPairing (fun u => F (u + b)) (fun u => F (u + a)) = autoCorr F (b - a) := by
    rw [testPairing_translate_pair F b a, show a - b = -(b - a) by ring, autoCorr_neg]
  -- the square of the three-term combination
  have hsq : 0 ≤ testPairing
      (fun u => (F u - lam * F (u + a)) - mu * F (u + b))
      (fun u => (F u - lam * F (u + a)) - mu * F (u + b)) :=
    testPairing_self_nonneg _
  rw [testPairing_sub_smul_sub_smul hX (hT b) hX (hT b) mu,
    testPairing_sub_smul_sub_smul hFn (hT a) hFn (hT a) lam,
    testPairing_sub_smul_left hFn (hT a) (hT b) lam,
    testPairing_comm (fun u => F (u + b)) (fun u => F u - lam * F (u + a)),
    testPairing_sub_smul_left hFn (hT a) (hT b) lam] at hsq
  simp only [q00, q0a, q0b, qa0, qaa, qbb, qab] at hsq
  linarith only [hsq]

/-- **The sharp two-atom law.** For all shifts,

    (A(a) + A(b))² ≤ 2 A(0) (A(0) + A(b − a)),

obtained from the three-shift Gram law at the diagonal weight by the discriminant. In the first open
window, with `a = log 2`, `b = log 3`, the two atoms of the cost side are jointly priced by the mass
and the charge at the free ratio lag `log(3/2)`: the ceiling `2 A(0)` is reachable only at full
resonance there. -/
theorem sq_two_atom_le (hF : Continuous F) (hFc : HasCompactSupport F) (a b : ℝ) :
    (autoCorr F a + autoCorr F b) ^ 2
      ≤ 2 * autoCorr F 0 * (autoCorr F 0 + autoCorr F (b - a)) := by
  -- the diagonal slice is a nonnegative quadratic in the common weight
  have hquad : ∀ θ : ℝ, 0 ≤ (2 * autoCorr F 0 + 2 * autoCorr F (b - a)) * (θ * θ)
      + (-2 * (autoCorr F a + autoCorr F b)) * θ + autoCorr F 0 := by
    intro θ
    have h := three_shift_gram hF hFc θ θ a b
    nlinarith [h]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

end GaloisForLFunctions.ArithmeticIncidencePositivity
