/-
# Exponent pairs specialized to Bourgain's logarithmic phase

This file fixes the exact uniform statement needed by the critical-line zeta
argument.  It is deliberately specialized to the phase `n ↦ n⁻ⁱᵗ`: this
avoids hiding smoothness conventions for a general exponent-pair class.

For `M/2 ≤ a < b ≤ M ≤ t`, `HasLogExponentPair κ λ` means

  `‖∑_{a<n≤b} n⁻ⁱᵗ‖ ≤ Cε (t/M)^(κ+ε) M^(λ+ε)`.

The main theorem proves the exact algebraic consequence of Bourgain's pair
`(13/84,55/84)`: the powers of `M` collapse to `1/2`, with no extra epsilon.
The deep proof that this pair has the stated property belongs to the
decoupling/spacing modules; this module only provides their typed target and
the zeta-facing connector.
-/
import GaloisForLFunctions.RHTower.BourgainExponentEndgame
import GaloisForLFunctions.RHTower.BourgainPartialSummation

open Complex

namespace RHTower

/-- Bourgain's unweighted logarithmic phase on positive natural numbers. -/
noncomputable def bourgainLogPhase (t : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (-Complex.I * (t : ℂ))

/-- A half-open logarithmic exponential sum. -/
noncomputable def bourgainLogIntervalSum
    (t : ℝ) (a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc a b, bourgainLogPhase t n

/-- Uniform exponent-pair estimate for the exact logarithmic phase used by
the zeta argument.  Bounds are required for every subinterval of a dyadic
block, not merely for the full block. -/
def HasLogExponentPair (κ ell : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ (t : ℝ) (M a b : ℕ),
        2 ≤ t →
        1 ≤ M →
        (M : ℝ) ≤ t →
        M / 2 ≤ a →
        a < b →
        b ≤ M →
        ‖bourgainLogIntervalSum t a b‖ ≤
          C * (t / (M : ℝ)) ^ (κ + ε) * (M : ℝ) ^ (ell + ε)

/-- Bourgain's published exponent pair. -/
noncomputable def bourgainExponentPair : ℝ × ℝ :=
  (13 / 84, 55 / 84)

@[simp] theorem bourgainExponentPair_fst :
    bourgainExponentPair.1 = bourgainZetaExponent := by
  simp [bourgainExponentPair, bourgainZetaExponent]

@[simp] theorem bourgainExponentPair_snd :
    bourgainExponentPair.2 = 55 / 84 := by
  simp [bourgainExponentPair]

/-- Exact power identity behind the passage from Bourgain's exponent pair to
his logarithmic block estimate. -/
theorem bourgain_exponentPair_power_identity
    {t M ε : ℝ} (ht : 0 < t) (hM : 0 < M) :
    (t / M) ^ (bourgainZetaExponent + ε) *
        M ^ ((55 / 84 : ℝ) + ε) =
      M ^ (1 / 2 : ℝ) * t ^ (bourgainZetaExponent + ε) := by
  have hpowM :
      M ^ ((55 / 84 : ℝ) + ε) /
          M ^ (bourgainZetaExponent + ε) =
        M ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_sub hM]
    congr 1
    simp only [bourgainZetaExponent]
    ring
  rw [Real.div_rpow ht.le hM.le]
  have hden :
      M ^ (bourgainZetaExponent + ε) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hM _)
  calc
    t ^ (bourgainZetaExponent + ε) /
          M ^ (bourgainZetaExponent + ε) *
        M ^ ((55 / 84 : ℝ) + ε) =
      t ^ (bourgainZetaExponent + ε) *
        (M ^ ((55 / 84 : ℝ) + ε) /
          M ^ (bourgainZetaExponent + ε)) := by
        field_simp
    _ = t ^ (bourgainZetaExponent + ε) * M ^ (1 / 2 : ℝ) := by
      rw [hpowM]
    _ = M ^ (1 / 2 : ℝ) * t ^ (bourgainZetaExponent + ε) := by ring

/-- The pair `(13/84,55/84)` gives the precise uniform logarithmic block
bound consumed by partial summation. -/
theorem logInterval_bound_of_bourgainExponentPair
    (hPair : HasLogExponentPair
      bourgainExponentPair.1 bourgainExponentPair.2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t : ℝ) (M a b : ℕ),
        2 ≤ t →
        1 ≤ M →
        (M : ℝ) ≤ t →
        M / 2 ≤ a →
        a < b →
        b ≤ M →
        ‖bourgainLogIntervalSum t a b‖ ≤
          C * (M : ℝ) ^ (1 / 2 : ℝ) *
            t ^ (bourgainZetaExponent + ε) := by
  obtain ⟨C, hC, hbound⟩ := hPair ε hε
  refine ⟨C, hC, ?_⟩
  intro t M a b ht hM hMt ha hab hb
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hMR0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h := hbound t M a b ht hM hMt ha hab hb
  rw [bourgainExponentPair_fst, bourgainExponentPair_snd] at h
  calc
    ‖bourgainLogIntervalSum t a b‖ ≤
        C * (t / (M : ℝ)) ^ (bourgainZetaExponent + ε) *
          (M : ℝ) ^ ((55 / 84 : ℝ) + ε) := h
    _ = C * ((t / (M : ℝ)) ^ (bourgainZetaExponent + ε) *
          (M : ℝ) ^ ((55 / 84 : ℝ) + ε)) := by ring
    _ = C * ((M : ℝ) ^ (1 / 2 : ℝ) *
          t ^ (bourgainZetaExponent + ε)) := by
      rw [bourgain_exponentPair_power_identity ht0 hMR0]
    _ = C * (M : ℝ) ^ (1 / 2 : ℝ) *
          t ^ (bourgainZetaExponent + ε) := by ring

/-- The logarithmic interval notation unfolds to the phase sum required by
the existing finite Abel-summation theorem. -/
theorem bourgainLogIntervalSum_eq_cpow
    (t : ℝ) (a b : ℕ) :
    bourgainLogIntervalSum t a b =
      ∑ n ∈ Finset.Ioc a b,
        (n : ℂ) ^ (-Complex.I * (t : ℂ)) := by
  rfl

end RHTower
