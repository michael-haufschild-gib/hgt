import Mathlib.Tactic

/-!
# Structured mutational genesis

This module formalizes a minimal mechanism strictly between two already certified vacuity
boundaries for endogenous law change.  One fixed rank-two exchange law has a period-two visible
rulebook and an open semantic lineage.  A transported certificate forces linearization, so the
open history is predicted by local exchange rather than stored in an arbitrary transition oracle.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The semantic lineage selected by the affine rank-two mutation, in denominator-free form. -/
def mutationalLineage : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 3 * mutationalLineage (n + 1) - mutationalLineage n

@[simp] theorem mutationalLineage_zero : mutationalLineage 0 = 1 := rfl

@[simp] theorem mutationalLineage_one : mutationalLineage 1 = 1 := rfl

@[simp] theorem mutationalLineage_two : mutationalLineage 2 = 2 := by
  norm_num [mutationalLineage]

/-- The certificate forces one constant-coefficient recurrence. -/
theorem mutationalLineage_recurrence (n : ℕ) :
    mutationalLineage (n + 2) =
      3 * mutationalLineage (n + 1) - mutationalLineage n := by
  rw [mutationalLineage]

/-- The Cassini residual is conserved and equals one. -/
theorem mutationalLineage_cassini (n : ℕ) :
    mutationalLineage (n + 2) * mutationalLineage n -
      mutationalLineage (n + 1) ^ 2 = 1 := by
  induction n with
  | zero => norm_num [mutationalLineage]
  | succ n ih =>
      change mutationalLineage (n + 3) * mutationalLineage (n + 1) -
          mutationalLineage (n + 2) ^ 2 = 1
      have hnext := mutationalLineage_recurrence (n + 1)
      have hnow := mutationalLineage_recurrence n
      change mutationalLineage (n + 3) =
        3 * mutationalLineage (n + 2) - mutationalLineage (n + 1) at hnext
      rw [hnext, hnow]
      rw [hnow] at ih
      ring_nf at ih ⊢
      exact ih

/-- The linearized lineage reconstructs the nonlinear exchange exactly. -/
theorem mutationalLineage_exchange (n : ℕ) :
    mutationalLineage (n + 2) * mutationalLineage n =
      mutationalLineage (n + 1) ^ 2 + 1 := by
  nlinarith [mutationalLineage_cassini n]

/-- Denominator-free form of the transported certificate `H = 3`. -/
theorem mutationalLineage_certificate (n : ℕ) :
    mutationalLineage n ^ 2 + mutationalLineage (n + 1) ^ 2 + 1 =
      3 * mutationalLineage n * mutationalLineage (n + 1) := by
  have hexchange := mutationalLineage_exchange n
  rw [mutationalLineage_recurrence n] at hexchange
  nlinarith

/-- Local exchange transports the numerator of the semantic certificate to either adjacent
pair.  Division is deliberately absent. -/
theorem mutationalCertificate_transport (a b c : ℤ)
    (hexchange : a * c = b ^ 2 + 1) :
    a ^ 2 + b ^ 2 + 1 = a * (a + c) ∧
      b ^ 2 + c ^ 2 + 1 = c * (a + c) := by
  constructor <;> nlinarith

/-- Exchange plus certificate value three forces the linear successor. -/
theorem mutationalExchange_certificate_forces_linearization
    (a b c : ℤ) (ha : a ≠ 0)
    (hexchange : a * c = b ^ 2 + 1)
    (hcertificate : a ^ 2 + b ^ 2 + 1 = 3 * a * b) :
    c = 3 * b - a := by
  apply mul_left_cancel₀ ha
  nlinarith

/-- After the initial seed, the semantic lineage is positive and strictly increasing. -/
theorem mutationalLineage_positive_increasing :
    ∀ n : ℕ,
      0 < mutationalLineage (n + 1) ∧
        mutationalLineage (n + 1) < mutationalLineage (n + 2) := by
  intro n
  induction n with
  | zero => norm_num [mutationalLineage]
  | succ n ih =>
      change 0 < mutationalLineage (n + 2) ∧
        mutationalLineage (n + 2) < mutationalLineage (n + 3)
      have hnext := mutationalLineage_recurrence (n + 1)
      change mutationalLineage (n + 3) =
        3 * mutationalLineage (n + 2) - mutationalLineage (n + 1) at hnext
      constructor
      · exact ih.1.trans ih.2
      · nlinarith [ih.1, ih.2]

/-- Every post-initial mutation more than doubles the preceding semantic response. -/
theorem mutationalLineage_more_than_double (n : ℕ) :
    2 * mutationalLineage (n + 2) < mutationalLineage (n + 3) := by
  have hrec := mutationalLineage_recurrence (n + 1)
  change mutationalLineage (n + 3) =
    3 * mutationalLineage (n + 2) - mutationalLineage (n + 1) at hrec
  have h := mutationalLineage_positive_increasing n
  nlinarith [h.1, h.2]

/-- The shifted lineage is strictly monotone. -/
theorem mutationalLineage_strictMono :
    StrictMono (fun n : ℕ => mutationalLineage (n + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (mutationalLineage_positive_increasing n).2

/-- An explicit lower bound used to certify semantic escape. -/
theorem mutationalLineage_index_lower (n : ℕ) :
    (n : ℤ) + 1 ≤ mutationalLineage (n + 1) := by
  induction n with
  | zero => norm_num [mutationalLineage]
  | succ n ih =>
      have hstep := (mutationalLineage_positive_increasing n).2
      change (n : ℤ) + 2 ≤ mutationalLineage (n + 2)
      omega

/-- Every natural threshold has a canonically indexed lineage witness beyond it. -/
theorem mutationalLineage_unbounded_witness (N : ℕ) :
    (N : ℤ) < mutationalLineage (N + 2) := by
  have hraw := mutationalLineage_index_lower (N + 1)
  have h : (N : ℤ) + 2 ≤ mutationalLineage (N + 2) := by
    norm_num [Nat.cast_add] at hraw ⊢
    exact hraw
  omega

/-- No positive period can close the semantic lineage. -/
theorem mutationalLineage_has_no_positive_period (p : ℕ) (hp : 0 < p) :
    ∃ n : ℕ,
      mutationalLineage (n + p + 1) ≠ mutationalLineage (n + 1) := by
  refine ⟨0, ?_⟩
  simpa only [zero_add] using ne_of_gt (mutationalLineage_strictMono hp)

/-- The observer retains only the alternating compatibility orientation. -/
def visibleMutationRule (n : ℕ) : ℤ := (-1) ^ n

@[simp] theorem visibleMutationRule_succ (n : ℕ) :
    visibleMutationRule (n + 1) = -visibleMutationRule n := by
  simp [visibleMutationRule, pow_succ]

/-- The visible rulebook has exact period two. -/
theorem visibleMutationRule_period_two (n : ℕ) :
    visibleMutationRule (n + 2) = visibleMutationRule n := by
  simp [visibleMutationRule, pow_add]

theorem visibleMutationRule_not_period_one :
    visibleMutationRule 1 ≠ visibleMutationRule 0 := by
  norm_num [visibleMutationRule]

/-- Closed certificate for structured endogenous genesis: recurrent compatibility, exact nonlinear
exchange, transported certificate, and open predictable lineage coexist in one fixed process. -/
theorem constitutiveMutationalGenesisMechanism_closed :
    (∀ n, visibleMutationRule (n + 2) = visibleMutationRule n) ∧
    (∀ n, mutationalLineage (n + 2) * mutationalLineage n =
      mutationalLineage (n + 1) ^ 2 + 1) ∧
    (∀ n, mutationalLineage n ^ 2 + mutationalLineage (n + 1) ^ 2 + 1 =
      3 * mutationalLineage n * mutationalLineage (n + 1)) ∧
    (∀ N : ℕ, (N : ℤ) < mutationalLineage (N + 2)) := by
  exact ⟨visibleMutationRule_period_two, mutationalLineage_exchange,
    mutationalLineage_certificate, mutationalLineage_unbounded_witness⟩

end GaloisForLFunctions.HTGeometry
