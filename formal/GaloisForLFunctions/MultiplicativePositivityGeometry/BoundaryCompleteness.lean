import GaloisForLFunctions.MultiplicativePositivityGeometry.ArithmeticRealization
import GaloisForLFunctions.MultiplicativePositivityGeometry.ProgressionModels

/-!
# Completeness of the boundary invariants

A boundary datum can have four invariants:

* **(N)** nonnegative weights;
* **(Z)** an integer divisor;
* **(S)** a simple pole, `D(0) = 1`;
* **(I)** pole isolation, `D ≤ 0` off the origin.

Together they force `D = 1_{0}`: no boundary zeros (`boundary_forcing_law`). None of them can be
dropped. Each has a realized datum that keeps the other three and has a boundary zero:

* without (I): the alternating one-prime factor, a simple pole at `0`, a zero at `1` and a pole at
  `2` (`isolation_necessary`);
* without (S): `ζ(s)²/(ζ(s+i)ζ(s−i))`, a double pole and zeros at `±1`
  (`simplicity_necessary`);
* without (Z): `ζ(s)/√(ζ(s+i)ζ(s−i))`, the twist by `1 − cos θ`, with half zeros at `±1`
  (`integrality_necessary`);
* without (N): `ζ(s)/(ζ(s+i)ζ(s−i))`, the twist by `1 − 2cos θ`. It has an integer divisor, a
  simple pole and simple zeros at `±1`. Its divisor is not positive definite, and its weights take
  negative values (`nonnegativity_necessary`).

`boundary_trichotomy_realized` realizes each type of the simple-pole trichotomy by an explicit
datum: `ζ`, the lattice factor and the alternating factor.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- **Boundary forcing law.** (N), (Z), (S) and (I) force `D = 1_{0}`. -/
theorem boundary_forcing_law {ι : Type*} {lam : ι → ℝ} {w : ℝ → ι → ℝ} {D : ℝ → ℝ}
    (hD : IsBoundaryDivisor lam w D) (h0 : D 0 = 1) (hint : ∀ u, ∃ n : ℤ, D u = n)
    (hnp : ∀ u, u ≠ 0 → D u ≤ 0) (u : ℝ) : D u = if u = 0 then 1 else 0 :=
  boundary_eq_delta_of_no_pole hD.isEvenPosDef h0 hint hnp u

/-! ### Degree-one twists -/

/-- A degree-one twist with integer `a₀` and `a₁/2` has an integer divisor. -/
theorem twistedDivisor_one_intValued {a : ℕ → ℝ} {p q : ℤ} (hp : a 0 = p) (hq : a 1 / 2 = q)
    (t₀ u : ℝ) : ∃ n : ℤ, twistedDivisor a 1 t₀ u = n := by
  refine ⟨p * (if u = 0 then 1 else 0) +
    q * ((if u + t₀ = 0 then 1 else 0) + (if u - t₀ = 0 then 1 else 0)), ?_⟩
  unfold twistedDivisor diracAt
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, zero_mul,
    add_zero, sub_zero, Nat.cast_one, one_mul]
  push_cast
  rw [← hp, ← hq]
  split_ifs <;> ring

/-- A twist whose higher coefficients are nonpositive has no boundary pole off the origin. -/
theorem twistedDivisor_nonpos {a : ℕ → ℝ} {K : ℕ} (ha : ∀ k, 1 ≤ k → a k ≤ 0) (t₀ : ℝ) {u : ℝ}
    (hu : u ≠ 0) : twistedDivisor a K t₀ u ≤ 0 := by
  unfold twistedDivisor
  refine Finset.sum_nonpos fun k _ => ?_
  have hd : ∀ v, 0 ≤ diracAt v := fun v => by unfold diracAt; split_ifs <;> norm_num
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [diracAt, hu]
  · have := ha k hk
    have h2 := add_nonneg (hd (u + k * t₀)) (hd (u - k * t₀))
    nlinarith

theorem twistedDivisor_one_at_one (a : ℕ → ℝ) : twistedDivisor a 1 1 1 = a 1 / 2 := by
  have := twistedDivisor_mul a (K := 1) (m := 1) le_rfl le_rfl one_ne_zero
  simpa only [Nat.cast_one, one_mul] using this

/-! ### (I) Pole isolation -/

/-- **Pole isolation is necessary.** The alternating one-prime factor has nonnegative weights, an
integer divisor and a simple pole at `0`, and a boundary zero at `1`; the forced pole sits at
`2`. -/
theorem isolation_necessary :
    ∃ (lam : ℕ → ℝ) (w : ℝ → ℕ → ℝ) (D : ℝ → ℝ), IsBoundaryDivisor lam w D ∧ D 0 = 1 ∧
      (∀ u, ∃ n : ℤ, D u = n) ∧ D 1 = -1 ∧ D 2 = 1 := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨hB, hk, hoff⟩ := alternating_isBoundaryDivisor h2π
  have e : 2 * Real.pi / (2 * Real.pi) = 1 := div_self h2π.ne'
  have hk' : ∀ k : ℤ, progressionDivisor (2 * Real.pi) (2 * Real.pi / 2) k = (-1) ^ k.natAbs :=
    fun k => by simpa only [e, mul_one] using hk k
  refine ⟨_, _, _, hB, ?_, fun u => ?_, ?_, ?_⟩
  · simpa using hk' 0
  · by_cases hu : ∃ k : ℤ, u = k * (2 * Real.pi / (2 * Real.pi))
    · obtain ⟨k, rfl⟩ := hu
      rw [e, mul_one, hk' k]
      exact ⟨(-1) ^ k.natAbs, by push_cast; rfl⟩
    · exact ⟨0, by rw [hoff u hu]; simp⟩
  · simpa using hk' 1
  · simpa using hk' 2

/-! ### (S) Pole simplicity -/

theorem doublePoleProfile_intValued (t₀ u : ℝ) : ∃ n : ℤ, doublePoleProfile t₀ u = n :=
  twistedDivisor_one_intValued (p := 2) (q := -1) (by simp [doublePoleCoeff])
    (by norm_num [doublePoleCoeff]) t₀ u

/-- **Pole simplicity is necessary.** `ζ(s)²/(ζ(s+i)ζ(s−i))` has nonnegative weights, an
integer divisor and no off-origin pole, yet boundary zeros at `±1`. -/
theorem simplicity_necessary :
    ∃ (lam : ℕ → ℝ) (w : ℝ → ℕ → ℝ) (D : ℝ → ℝ), IsBoundaryDivisor lam w D ∧ D 0 = 2 ∧
      (∀ u, ∃ n : ℤ, D u = n) ∧ (∀ u, u ≠ 0 → D u ≤ 0) ∧ D 1 = -1 :=
  ⟨_, _, _, doublePoleProfile_isBoundaryDivisor 1, doublePoleProfile_zero one_ne_zero,
    doublePoleProfile_intValued 1, fun _ hu => doublePoleProfile_nonpos one_ne_zero hu,
    doublePoleProfile_has_zero one_ne_zero⟩

/-! ### (Z) Integrality -/

/-- Coefficients of `1 − cos θ`. -/
def halfZeroCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => -1
  | _ => 0

theorem halfZeroCoeff_nonneg_poly (θ : ℝ) :
    0 ≤ HTGeometry.cosinePolynomial halfZeroCoeff 1 θ := by
  simp only [HTGeometry.cosinePolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
    halfZeroCoeff]
  push_cast
  simp only [zero_mul, Real.cos_zero, one_mul]
  linarith [Real.cos_le_one θ]

/-- **Integrality is necessary.** The twist by `1 − cos θ` has nonnegative weights, a simple pole
and no off-origin pole, yet half zeros `D(±1) = −1/2`. -/
theorem integrality_necessary :
    ∃ (lam : ℕ → ℝ) (w : ℝ → ℕ → ℝ) (D : ℝ → ℝ), IsBoundaryDivisor lam w D ∧ D 0 = 1 ∧
      (∀ u, u ≠ 0 → D u ≤ 0) ∧ D 1 = -1 / 2 := by
  refine ⟨_, _, _, twisted_isBoundaryDivisor halfZeroCoeff_nonneg_poly 1,
    twistedDivisor_zero _ _ one_ne_zero, fun u hu => twistedDivisor_nonpos ?_ 1 hu, ?_⟩
  · intro k hk
    rcases k with _ | _ | k
    · omega
    · norm_num [halfZeroCoeff]
    · simp [halfZeroCoeff]
  · rw [twistedDivisor_one_at_one]
    norm_num [halfZeroCoeff]

/-! ### (N) Nonnegativity -/

/-- Coefficients of `1 − 2cos θ`. -/
def signedCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => -2
  | _ => 0

theorem signedCoeff_higher_nonpos (k : ℕ) (hk : 1 ≤ k) : signedCoeff k ≤ 0 := by
  rcases k with _ | _ | k
  · omega
  · norm_num [signedCoeff]
  · simp [signedCoeff]

/-- The boundary divisor of `ζ(s)/(ζ(s+i)ζ(s−i))`: `δ₀ − δ₁ − δ₋₁`. It is not positive definite,
since a simple zero at `1` would force a pole at `2`. -/
theorem signedTwist_not_posDef : ¬ IsEvenPosDef (twistedDivisor signedCoeff 1 1) := by
  intro hD
  have h0 : twistedDivisor signedCoeff 1 1 0 = 1 := twistedDivisor_zero _ _ one_ne_zero
  have h1 : twistedDivisor signedCoeff 1 1 1 = -1 := by
    rw [twistedDivisor_one_at_one]; norm_num [signedCoeff]
  have h2 : twistedDivisor signedCoeff 1 1 (1 + 1) = -twistedDivisor signedCoeff 1 1 1 :=
    hD.apply_add_of_eq_neg (by rw [h0, h1]) 1
  have h2' : twistedDivisor signedCoeff 1 1 (1 + 1) = 0 := by
    refine twistedDivisor_eq_zero _ _ fun k hk => ?_
    interval_cases k <;> norm_num
  rw [h2', h1] at h2
  norm_num at h2

/-- The signed twist has negative weights: with nonnegative weights it would be a boundary datum,
hence positive definite. -/
theorem signedTwist_weight_not_nonneg :
    ¬ ∀ x, 0 < x → ∀ n, 0 ≤ twistedWeight signedCoeff 1 1 x n := by
  intro hnn
  have hB : IsBoundaryDivisor logFrequency (twistedWeight signedCoeff 1 1)
      (twistedDivisor signedCoeff 1 1) :=
    { nonneg := hnn
      summable := fun x hx => Summable.of_nonneg_of_le (hnn x hx)
        (fun n => mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (abs_cosinePolynomial_le _ _ _))
          (zetaBoundaryWeight_nonneg x n))
        ((summable_zetaBoundaryWeight hx).mul_right
          (∑ k ∈ Finset.range (1 + 1), |signedCoeff k|))
      tendsto := tendsto_twistedTrace _ _ _ }
  exact signedTwist_not_posDef hB.isEvenPosDef

/-- **Nonnegativity is necessary.** The signed twist `ζ(s)/(ζ(s+i)ζ(s−i))` has boundary limits
with an integer divisor, a simple pole and no off-origin pole, yet a simple zero at `1`; its weights
are not all nonnegative. -/
theorem nonnegativity_necessary :
    ∃ (lam : ℕ → ℝ) (w : ℝ → ℕ → ℝ) (D : ℝ → ℝ),
      (∀ u, Tendsto (fun x => x * cosineTrace (w x) lam u) (𝓝[>] 0) (𝓝 (D u))) ∧ D 0 = 1 ∧
      (∀ u, ∃ n : ℤ, D u = n) ∧ (∀ u, u ≠ 0 → D u ≤ 0) ∧ D 1 = -1 ∧
      ¬ IsEvenPosDef D ∧ ¬ ∀ x, 0 < x → ∀ n, 0 ≤ w x n :=
  ⟨logFrequency, twistedWeight signedCoeff 1 1, twistedDivisor signedCoeff 1 1,
    tendsto_twistedTrace _ _ _, twistedDivisor_zero _ _ one_ne_zero,
    twistedDivisor_one_intValued (p := 1) (q := -1) (by simp [signedCoeff])
      (by norm_num [signedCoeff]) 1,
    fun _ hu => twistedDivisor_nonpos signedCoeff_higher_nonpos 1 hu,
    by rw [twistedDivisor_one_at_one]; norm_num [signedCoeff],
    signedTwist_not_posDef, signedTwist_weight_not_nonneg⟩

/-! ### The trichotomy is realized -/

open Classical in
/-- **Each trichotomy type occurs.** `ζ` realizes `1_{0}`; for every `c > 0` the one-prime factors
with step `2π/c` realize the lattice indicator of `cℤ` and the alternating character on `cℤ`. -/
theorem boundary_trichotomy_realized {c : ℝ} (hc : 0 < c) :
    IsBoundaryDivisor logFrequency zetaBoundaryWeight (fun u => if u = 0 then 1 else 0) ∧
    (∃ (lam : ℕ → ℝ) (w : ℝ → ℕ → ℝ),
      IsBoundaryDivisor lam w (fun u => if ∃ k : ℤ, u = k * c then 1 else 0)) ∧
    (∃ (lam : ℕ → ℝ) (w : ℝ → ℕ → ℝ) (D : ℝ → ℝ), IsBoundaryDivisor lam w D ∧
      (∀ k : ℤ, D (k * c) = (-1) ^ k.natAbs) ∧ ∀ u, (¬ ∃ k : ℤ, u = k * c) → D u = 0) := by
  have hh : 0 < 2 * Real.pi / c := by positivity
  have e : 2 * Real.pi / (2 * Real.pi / c) = c := by field_simp
  refine ⟨?_, ⟨progressionFrequency (2 * Real.pi / c) (2 * Real.pi / c),
    progressionWeight (2 * Real.pi / c) (2 * Real.pi / c), ?_⟩, ?_⟩
  · convert zeta_isBoundaryDivisor using 1
    funext u
    rw [zetaBoundaryDivisor_eq]
  · convert lattice_isBoundaryDivisor hh using 1
    funext u
    by_cases hu : ∃ k : ℤ, u = k * c
    · rw [if_pos hu, if_pos (by rwa [e])]
    · rw [if_neg hu, if_neg (by rwa [e])]
  · obtain ⟨hB, hk, hoff⟩ := alternating_isBoundaryDivisor hh
    exact ⟨_, _, _, hB, fun k => by simpa only [e] using hk k,
      fun u hu => hoff u (by rwa [e])⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
