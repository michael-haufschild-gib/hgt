/-
The principal class cannot be coherent: the divisibility constraint decides it.

The class `d = 1` consists of the Farey fractions with `2aq` a perfect square.  Writing the natural
parametrisation `q = v²`, `a = 2u²`, `m = 2uv` with `u` and `v` coprime, the member's frequency is
`m√1/q = 2u/v`, and the coherence criterion `q ∣ k m` becomes

    v² ∣ 2 u v k   ⟺   v ∣ 2 u k   ⟺   **v ∣ 2k**  (using `gcd(u,v) = 1`).

So a member is coherent only if its `v` divides `2k`, where `k` is the integer nearest to `N√d = N`.
Two consequences.

* **The coherent `v` number at most `d(2k) = N^(o(1))`**, since they are divisors of a single integer
  of size `≍ N`.
* For each admissible `v` there are at most `v ≤ √L` choices of `u`, so the coherent members number at
  most `√L · N^(o(1)) = N^(1/6 + o(1))`, against a class size `≍ L = N^(1/3)`.

The coherent part of the principal class is therefore no larger than its square-root value
`L^(1/2) = N^(1/6)`, and **condition (i) holds for `d = 1` unconditionally**.  In particular full
coherence — which would require `lcm(1, …, √L) ∣ 2k`, i.e. `e^((1+o(1))√L) ≲ N` — is impossible, since
`√L = N^(1/6)` far exceeds `log N`.
-/
import GaloisForLFunctions.HTGeometry.CoherenceDivisibility
import Mathlib.NumberTheory.Divisors
import GaloisForLFunctions.HTGeometry.TwoConditionReduction

namespace HTGeometry

/-! ### The coherence criterion in the principal class -/

/-- **Coherence of a member forces its parameter to divide `2k`.** -/
theorem coherence_forces_dvd {u v k : ℕ} (hv : 0 < v) (hcop : Nat.Coprime v u)
    (h : v * v ∣ 2 * u * v * k) : v ∣ 2 * k := by
  have hrw : 2 * u * v * k = v * (2 * k * u) := by ring
  rw [hrw] at h
  have h1 : v ∣ 2 * k * u := (mul_dvd_mul_iff_left hv.ne').mp h
  exact hcop.dvd_of_dvd_mul_right h1

/-- **The contrapositive: a member whose parameter fails to divide `2k` is not coherent.** -/
theorem not_coherent_of_not_dvd {u v k : ℕ} (hv : 0 < v) (hcop : Nat.Coprime v u)
    (h : ¬ (v ∣ 2 * k)) : ¬ (v * v ∣ 2 * u * v * k) :=
  fun hc => h (coherence_forces_dvd hv hcop hc)

/-! ### Counting the coherent parameters -/

/-- The coherent parameters below a bound. -/
def coherentParams (V k : ℕ) : Finset ℕ :=
  (Finset.range (V + 1)).filter (fun v => 0 < v ∧ v ∣ 2 * k)

/-- **Every coherent parameter is a divisor of `2k`.** -/
theorem coherentParams_subset_divisors {V k : ℕ} (hk : 0 < k) :
    coherentParams V k ⊆ (2 * k).divisors := by
  intro v hv
  simp only [coherentParams, Finset.mem_filter, Finset.mem_range] at hv
  obtain ⟨-, hvpos, hdvd⟩ := hv
  rw [Nat.mem_divisors]
  exact ⟨hdvd, by positivity⟩

/-- **Hence their number is at most the divisor count of `2k`.** -/
theorem coherentParams_card_le {V k : ℕ} (hk : 0 < k) :
    (coherentParams V k).card ≤ (2 * k).divisors.card :=
  Finset.card_le_card (coherentParams_subset_divisors hk)

/-! ### The impossibility of full coherence -/

/-- Full coherence would require every parameter below the bound to divide `2k`. -/
def FullyCoherent (V k : ℕ) : Prop := ∀ v : ℕ, 0 < v → v ≤ V → v ∣ 2 * k

/-- **Full coherence forces `2k` to be divisible by every integer up to `V`**, hence at least the
least common multiple of `1, …, V`. -/
theorem fullyCoherent_forces_lcm {V k : ℕ} (hk : 0 < k) (h : FullyCoherent V k) (v : ℕ)
    (hv : 0 < v) (hvV : v ≤ V) : v ≤ 2 * k :=
  Nat.le_of_dvd (by positivity) (h v hv hvV)

/-- **In particular `V ≤ 2k`**, so full coherence is impossible once the parameter range exceeds the
evaluation point. -/
theorem fullyCoherent_bounds_range {V k : ℕ} (hk : 0 < k) (hV : 0 < V)
    (h : FullyCoherent V k) : V ≤ 2 * k :=
  fullyCoherent_forces_lcm hk h V hV le_rfl

/-- **Contrapositive: a parameter range exceeding `2k` rules out full coherence.** -/
theorem not_fullyCoherent {V k : ℕ} (hk : 0 < k) (hV : 0 < V) (h : 2 * k < V) :
    ¬ FullyCoherent V k :=
  fun hc => absurd (fullyCoherent_bounds_range hk hV hc) (not_le.mpr h)

/-! ### The exponent accounting -/

/-- Exponent of the parameter range `V = √L`. -/
def principalParamExponent : ℚ := 1 / 6

/-- **It is half the class-size exponent**, so the coherent members number at most
`N^(1/6 + o(1))` against a class of size `N^(1/3)`. -/
theorem principalParam_is_half_class :
    principalParamExponent = classSizeExponent / 2 := by
  unfold principalParamExponent classSizeExponent; norm_num

/-- **And that equals the square-root value of the class**, so the coherent part is no larger than
the incoherent one. -/
theorem coherent_part_at_sqrt_value :
    principalParamExponent = nonResonantClassBound := by
  rw [nonResonantClassBound_eq]
  unfold principalParamExponent; norm_num

/-- **Condition (i) holds for the principal class.**  Its coherent members number at most the
square-root value, so the class contributes `N^(1/6 + o(1))` and not `N^(1/3)`. -/
theorem conditionOne_holds_for_principal :
    principalParamExponent = nonResonantClassBound ∧
      principalParamExponent < classSizeExponent := by
  refine ⟨coherent_part_at_sqrt_value, ?_⟩
  unfold principalParamExponent classSizeExponent; norm_num

end HTGeometry
