import Mathlib.Data.List.Basic

/-!
# Differential-jet pole fingerprints

For a pole of order `m`, the leading coefficient of the `j`-th derivative contains the rising
factorial `(m)ⱼ`.  If a differential monomial has jet-exponent list
`[β₀, β₁, ..., βₙ]`, unique factorization of the product of rising factorials records the suffix
sums

`[Σ_{j≥0} βⱼ, Σ_{j≥1} βⱼ, ..., βₙ]`.

The first coordinate is the total degree; the later coordinates are the multiplicities of the
linear factors `m`, `m+1`, and so on.  This file proves that the resulting pole fingerprint loses
no jet-exponent information.  It is the finite combinatorial core needed by divisor-valuation
approaches to differential independence.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Successive suffix sums of a finite differential-jet exponent list.  These are exactly the
total-degree and rising-factor multiplicities in the leading coefficient at a variable-order
pole. -/
def jetPoleFingerprint : List ℕ → List ℕ
  | [] => []
  | exponent :: tail =>
      (exponent + tail.sum) :: jetPoleFingerprint tail

/-- **Jet pole-fingerprint law.**  Total pole degree together with all rising-factor
multiplicities uniquely determines the complete finite differential-jet exponent vector. -/
theorem jetPoleFingerprint_injective : Function.Injective jetPoleFingerprint := by
  intro exponents
  induction exponents with
  | nil =>
      intro other h
      cases other with
      | nil => rfl
      | cons exponent tail => simp [jetPoleFingerprint] at h
  | cons exponent tail ih =>
      intro other h
      cases other with
      | nil => simp [jetPoleFingerprint] at h
      | cons otherExponent otherTail =>
          have htail :
              jetPoleFingerprint tail = jetPoleFingerprint otherTail :=
            (List.cons.inj h).2
          have htails : tail = otherTail := ih htail
          subst otherTail
          have hhead :
              exponent + tail.sum = otherExponent + tail.sum :=
            (List.cons.inj h).1
          have hexponent : exponent = otherExponent :=
            Nat.add_right_cancel hhead
          subst otherExponent
          rfl

end GaloisForLFunctions.HTGeometry
