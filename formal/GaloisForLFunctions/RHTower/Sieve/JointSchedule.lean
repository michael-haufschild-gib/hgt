import GaloisForLFunctions.RHTower.Sieve.JointLadderDefectDivisor
import GaloisForLFunctions.RHTower.Sieve.JointLongRange
import GaloisForLFunctions.RHTower.Sieve.SpectralParameters
import GaloisForLFunctions.RHTower.Sieve.ScaledCardLength

/-!
# The parameter schedule of the joint arrangement

Both designated ranges of the `ω_P·ω_Q` arrangement are instances of the corpus's own ladder
parameters `Sieve/SpectralParameters.{ladderEta, ladderSteps, ladderTop}`, at two different exponent
pairs.  Writing `𝓁 = log x`:

| range | corpus instance | base | top | harmonic mass |
|-|-|-|-|-|
| short `P` | `(β, 1/2)` | `siftStart (β/2) x ≈ exp(𝓁^{β/2})` | `ladderTop β (1/2) x ≈ exp(𝓁^β)` | `(β/2)·log 𝓁 → ∞` |
| long `Q` | `Sieve/JointLongRange`, `9/10 < a < b < 1` | `siftStart a x ≈ exp(𝓁^a)` | `jointLongTopF a b x ≈ exp(𝓁^b)` | `(b−a)·log 𝓁 → ∞` |

so `tendsto_ladderMass`, `eventually_ladderTop_facts`, `ladderTop_bounds` and `ladderSteps_le` all
apply verbatim to each.  The two ranges are disjoint for large `x` because `β < 9/10 < a`.

What is genuinely new here is the pair `(Wc, T₀)`: the Gallagher cut `√x/h`, which makes
`δ·Wc ≤ 1`, and the expiry height `(√x/h)·𝓁^{β/2}`, which is the *low* height that §4 can supply and
Gallagher can consume — see the discussion in `Sieve/JointBudgetTermSplit`.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- The Gallagher cut of the joint arrangement. -/
def jointCut (c β x : ℝ) : ℝ := Real.sqrt x / scaledLength c β x

/-- The expiry height of the §4 estimate. -/
def jointExpiry (c β x : ℝ) : ℝ := jointCut c β x * (Real.log x) ^ (β / 2)

/-- The short designated range. -/
def jointShortSet (β x : ℝ) : Finset ℕ :=
  primesRange (siftStart (1 / 2 * β) x) (ladderTop β (1 / 2) x)

/-- The long designated range, at the ratio its own defect forces. -/
def jointLongSet (a b x : ℝ) : Finset ℕ := jointLongSetF a b x

/-! ## Elementary facts -/

theorem jointShortSet_prime (β x : ℝ) : ∀ p ∈ jointShortSet β x, p.Prime := fun _ hp =>
  (mem_primesRange.1 hp).1

theorem jointLongSet_prime (a b x : ℝ) : ∀ q ∈ jointLongSet a b x, q.Prime :=
  jointLongSetF_prime a b x

theorem jointShortSet_ge (β x : ℝ) :
    ∀ p ∈ jointShortSet β x, ((siftStart (1 / 2 * β) x : ℕ) : ℝ) ≤ (p : ℝ) := by
  intro p hp
  exact_mod_cast (mem_primesRange.1 hp).2.1.le

theorem jointLongSet_ge (a b x : ℝ) :
    ∀ q ∈ jointLongSet a b x, ((siftStart a x : ℕ) : ℝ) ≤ (q : ℝ) :=
  jointLongSetF_ge a b x

/-- **The short designated set is covered by its ladder.** -/
theorem jointShortSet_range {β x : ℝ} (hx : 1 < x) :
    ∀ p ∈ jointShortSet β x,
      ((siftStart (1 / 2 * β) x : ℕ) : ℝ) < (p : ℝ)
        ∧ (p : ℝ) ≤ ((siftStart (1 / 2 * β) x : ℕ) : ℝ)
            * (1 + ladderEta β (1 / 2) x) ^ (ladderSteps β (1 / 2) x) := by
  intro p hp
  obtain ⟨-, hlo, hhi⟩ := mem_primesRange.1 hp
  refine ⟨by exact_mod_cast hlo, ?_⟩
  have hη := ladderEta_pos (β := β) (γ := 1 / 2) hx
  have hfl : ((ladderTop β (1 / 2) x : ℕ) : ℝ)
      ≤ ((siftStart (1 / 2 * β) x : ℕ) : ℝ)
          * (1 + ladderEta β (1 / 2) x) ^ (ladderSteps β (1 / 2) x) := by
    rw [ladderTop]
    refine Nat.floor_le ?_
    have h1 : (0 : ℝ) ≤ ((siftStart (1 / 2 * β) x : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < (1 + ladderEta β (1 / 2) x) ^ (ladderSteps β (1 / 2) x) := by positivity
    positivity
  have hpc : (p : ℝ) ≤ ((ladderTop β (1 / 2) x : ℕ) : ℝ) := by exact_mod_cast hhi
  linarith

/-- **The long designated set is covered by its ladder.** -/
theorem jointLongSet_range {a b x : ℝ} (hx : 1 < x) :
    ∀ q ∈ jointLongSet a b x,
      ((siftStart a x : ℕ) : ℝ) < (q : ℝ)
        ∧ (q : ℝ) ≤ ((siftStart a x : ℕ) : ℝ) * (1 + jointLongEta a b x)
            ^ (gLadderSteps ((siftStart a x : ℕ) : ℝ) (jointLongEta a b x) (cardLength b x)) :=
  jointLongSetF_range hx

/-- **The two designated ranges are disjoint, eventually.**  The short one stops below
`exp(𝓁^β)` and the long one starts above `exp(𝓁^a)`, and `β < a`. -/
theorem eventually_jointSets_disjoint {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβa : β < a) :
    ∀ᶠ x : ℝ in atTop, Disjoint (jointShortSet β x) (jointLongSet a b x) := by
  have hγ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hγ1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hγβ : (1 : ℝ) / 2 * β < 1 := by nlinarith
  filter_upwards [eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hfacts hlog1
  refine Finset.disjoint_left.2 fun p hp hq => ?_
  obtain ⟨-, -, hple⟩ := mem_primesRange.1 hp
  obtain ⟨-, hqlo, -⟩ := mem_primesRange.1 hq
  have hple' : ((p : ℕ) : ℝ) ≤ cardLength β x := by
    have h1 : ((p : ℕ) : ℝ) ≤ ((ladderTop β (1 / 2) x : ℕ) : ℝ) := by exact_mod_cast hple
    linarith [hfacts.2.1]
  have hqlo' : ((siftStart a x : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hqlo
  have hge : Real.exp ((Real.log x) ^ a) ≤ ((siftStart a x : ℕ) : ℝ) := Nat.le_ceil _
  have hmono : (Real.log x) ^ β ≤ (Real.log x) ^ a :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hβa.le
  have hcl : cardLength β x ≤ Real.exp ((Real.log x) ^ a) := by
    rw [cardLength]
    exact Real.exp_le_exp.2 hmono
  linarith

/-! ## The harmonic masses -/

theorem jointShortSet_mass {β x : ℝ} (hz : siftStart (1 / 2 * β) x ≤ ladderTop β (1 / 2) x) :
    Joint.mass (jointShortSet β x)
      = mertensS (ladderTop β (1 / 2) x) - mertensS (siftStart (1 / 2 * β) x) := by
  rw [Joint.mass, jointShortSet, sum_inv_primesRange hz]

theorem jointLongSet_mass {a b x : ℝ} (hz : siftStart a x ≤ jointLongTopF a b x) :
    Joint.mass (jointLongSet a b x)
      = mertensS (jointLongTopF a b x) - mertensS (siftStart a x) := by
  rw [Joint.mass, jointLongSet, jointLongSetF, sum_inv_primesRange hz]

/-- **The short range's harmonic mass grows.** -/
theorem tendsto_jointShortMass {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => Joint.mass (jointShortSet β x)) atTop atTop := by
  have hγ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hγ1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hγβ : (1 : ℝ) / 2 * β < 1 := by nlinarith
  have hbase := tendsto_ladderMass hβ0 hγ0 hγ1 hγβ
  refine hbase.congr' ?_
  filter_upwards [eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ] with x hfacts
  exact (jointShortSet_mass hfacts.2.2).symm

/-- **The long range's harmonic mass grows.** -/
theorem tendsto_jointLongMass {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ => Joint.mass (jointLongSet a b x)) atTop atTop := by
  refine (tendsto_jointLongMassF ha0 hab).congr' ?_
  filter_upwards [eventually_siftStart_le_jointLongTopF ha0 hab] with x hz
  exact (jointLongSet_mass hz).symm

/-- **The joint harmonic mass is eventually positive.** -/
theorem eventually_jointMass_pos {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha0 : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop,
      0 < Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x) := by
  filter_upwards [(tendsto_jointShortMass hβ0 hβ1).eventually_gt_atTop 0,
    (tendsto_jointLongMass ha0 hab).eventually_gt_atTop 0] with x h1 h2
  exact mul_pos h1 h2

end

end RHTower.Sieve
