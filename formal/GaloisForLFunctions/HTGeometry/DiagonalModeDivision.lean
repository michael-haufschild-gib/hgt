import GaloisForLFunctions.HTGeometry.OrbitFreeness
import GaloisForLFunctions.HTGeometry.SecularWeldRigidity
import Mathlib.Data.Complex.BigOperators

/-!
# Diagonal mode division: the combination-mode lane of the secular weld

The diagonal dilation of the secular algebra scales the combination mode `χ_m`
(`m : ⊕_p ℤ`, one integer lane per prime) by the weight `w(m) = ∏_p p^{-m_p}`,
whose logarithm is minus the mode frequency `m·ℓ = Σ_p m_p·log p`.  All
statements here are unconditional.

* `modeFrequency_eq_zero_iff`, `modeFrequency_ne_zero` — no resonances: the
  frequency `m·ℓ` vanishes only for the trivial mode, by the `ℚ`-linear
  independence of the prime logarithms.  This is the qualitative floor that
  makes the mode-by-mode division defined; no effective lower bound on `|m·ℓ|`
  is used or claimed.
* `log_diagonalWeightReal`, `diagonalWeight_eq_one_iff` — the weight of the
  combination-mode lane is `e^{-m·ℓ}`; it equals `1` only at `m = 0`.
* `diagonal_mode_division` — the cohomological division equation: for `m ≠ 0`
  the mode `χ_m` is `(δ - id)` of `(w(m)-1)⁻¹ · χ_m`, with explicit
  nonvanishing divisor `w(m) - 1`.
* `diagonal_equivariant_kills_mode`, `no_diagonal_equivariant_retraction` —
  the rigidity instance through `equivariant_linear_kills_scaled`: a linear
  extraction equivariant under the single diagonal dilation annihilates every
  nonzero combination mode, and no equivariant algebra retraction onto the
  scalar block exists.

The quantitative small-divisor regularity (an effective lower bound on
`|m·ℓ|` for mixed-sign modes, Baker–Wüstholz) is classical input that is not
formalized here; nothing in this file depends on it.
-/

open scoped BigOperators

namespace GaloisForLFunctions

namespace SecularWeld

noncomputable section

/-- The combination-mode frequency `m·ℓ = Σ_p m_p·log p` of an exponent vector. -/
def modeFrequency (m : PrimeExponents) : ℝ :=
  m.sum fun p e => (e : ℝ) * Real.log ((p : ℕ) : ℝ)

/-- **No resonances.**  The mode frequency vanishes only on the trivial mode:
`Σ_p m_p·log p = 0` forces `m = 0`, by `ℚ`-linear independence of the prime
logarithms. -/
theorem modeFrequency_eq_zero_iff (m : PrimeExponents) :
    modeFrequency m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have h0 : ∑ p ∈ m.support, ((m p : ℚ)) • Real.log ((p : ℕ) : ℝ) = 0 := by
      rw [← h]
      simp only [modeFrequency, Finsupp.sum]
      exact Finset.sum_congr rfl fun p _ => by
        rw [Rat.smul_def]
        norm_num
    have hall := logPrime_no_rat_relation m.support (fun q => (m q : ℚ)) h0
    ext p
    rcases eq_or_ne (m p) 0 with hmp | hmp
    · simpa using hmp
    · have hp : p ∈ m.support := Finsupp.mem_support_iff.mpr hmp
      have hq : (m p : ℚ) = 0 := hall p hp
      have hz : m p = 0 := by exact_mod_cast hq
      simpa using hz
  · rintro rfl
    simp [modeFrequency]

/-- The divisor of the mode-by-mode division is defined: `m·ℓ ≠ 0` for `m ≠ 0`. -/
theorem modeFrequency_ne_zero {m : PrimeExponents} (hm : m ≠ 0) :
    modeFrequency m ≠ 0 :=
  fun h => hm ((modeFrequency_eq_zero_iff m).mp h)

/-- The diagonal weight of a combination mode, real form: `∏_p p^{-m_p}`. -/
def diagonalWeightReal (m : PrimeExponents) : ℝ :=
  m.prod fun p e => ((p : ℕ) : ℝ) ^ (-e)

theorem diagonalWeightReal_pos (m : PrimeExponents) : 0 < diagonalWeightReal m := by
  simp only [diagonalWeightReal, Finsupp.prod]
  refine Finset.prod_pos fun p _ => zpow_pos ?_ _
  exact_mod_cast p.2.pos

/-- **The weight of the combination-mode lane is `e^{-m·ℓ}`**: the logarithm of
the diagonal weight is minus the mode frequency. -/
theorem log_diagonalWeightReal (m : PrimeExponents) :
    Real.log (diagonalWeightReal m) = -(modeFrequency m) := by
  simp only [diagonalWeightReal, modeFrequency, Finsupp.prod, Finsupp.sum]
  rw [Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.log_zpow]
    push_cast
    ring
  · intro p _
    exact (zpow_pos (by exact_mod_cast p.2.pos : (0 : ℝ) < ((p : ℕ) : ℝ)) _).ne'

/-- The diagonal weight of a combination mode: `w(m) = ∏_p p^{-m_p}` in `ℂ`. -/
def diagonalWeight (m : PrimeExponents) : ℂ :=
  m.prod fun p e => ((p : ℕ) : ℂ) ^ (-e)

theorem diagonalWeight_eq_ofReal (m : PrimeExponents) :
    diagonalWeight m = ((diagonalWeightReal m : ℝ) : ℂ) := by
  simp only [diagonalWeight, diagonalWeightReal, Finsupp.prod]
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Complex.ofReal_zpow]
  congr 1

theorem diagonalWeight_zero : diagonalWeight 0 = 1 := by
  simp [diagonalWeight]

theorem diagonalWeight_add (m m' : PrimeExponents) :
    diagonalWeight (m + m') = diagonalWeight m * diagonalWeight m' := by
  simp only [diagonalWeight]
  rw [Finsupp.prod_add_index']
  · intro p
    simp
  · intro p e₁ e₂
    rw [neg_add]
    exact zpow_add₀ (primeCast_ne_zero p) _ _

/-- **Resonance-free dichotomy for the weight**: the diagonal weight is `1` only
on the trivial mode. -/
theorem diagonalWeight_eq_one_iff (m : PrimeExponents) :
    diagonalWeight m = 1 ↔ m = 0 := by
  constructor
  · intro h
    have hR : diagonalWeightReal m = 1 := by
      have hcast := diagonalWeight_eq_ofReal m
      rw [h] at hcast
      exact_mod_cast hcast.symm
    have hlog : -(modeFrequency m) = 0 := by
      rw [← log_diagonalWeightReal, hR, Real.log_one]
    exact (modeFrequency_eq_zero_iff m).mp (neg_eq_zero.mp hlog)
  · rintro rfl
    exact diagonalWeight_zero

/-- The combination-mode basis element `χ_m` of the secular algebra. -/
def secularMode (m : PrimeExponents) : SecularAlgebra :=
  AddMonoidAlgebra.of ℂ PrimeExponents (Multiplicative.ofAdd m)

/-- Every combination mode is a unit: `χ_m · χ_{-m} = 1`. -/
theorem secularMode_mul_neg (m : PrimeExponents) :
    secularMode m * secularMode (-m) = 1 := by
  unfold secularMode
  rw [← map_mul]
  have h : Multiplicative.ofAdd m * Multiplicative.ofAdd (-m) = 1 := by
    rw [← ofAdd_add]
    simp
  rw [h, map_one]

/-- The diagonal character `χ_m ↦ w(m)·χ_m` as a monoid homomorphism. -/
def diagonalChar : Multiplicative PrimeExponents →* SecularAlgebra where
  toFun m := diagonalWeight m.toAdd • AddMonoidAlgebra.of ℂ PrimeExponents m
  map_one' := by
    simp [diagonalWeight_zero, AddMonoidAlgebra.one_def]
  map_mul' x y := by
    rw [toAdd_mul, diagonalWeight_add, map_mul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- The diagonal dilation of the secular algebra: the `ℂ`-algebra endomorphism
scaling each combination mode by its weight `w(m)`.  On any finitely supported
mode it agrees with the corresponding finite product of prime dilations. -/
def diagonalDilation : SecularAlgebra →ₐ[ℂ] SecularAlgebra :=
  AddMonoidAlgebra.lift ℂ SecularAlgebra PrimeExponents diagonalChar

/-- Each combination mode is a `w(m)`-eigenvector of the diagonal dilation. -/
theorem diagonalDilation_mode (m : PrimeExponents) :
    diagonalDilation (secularMode m) = diagonalWeight m • secularMode m := by
  unfold diagonalDilation secularMode
  rw [AddMonoidAlgebra.lift_of]
  simp [diagonalChar]

/-- **The diagonal mode-division equation.**  For a nonzero combination mode the
cohomological equation `(δ - id) g = χ_m` is solved by the explicit division
`g = (w(m)-1)⁻¹ · χ_m`; the divisor `w(m) - 1` is nonzero because the mode
frequency `m·ℓ` does not resonate. -/
theorem diagonal_mode_division {m : PrimeExponents} (hm : m ≠ 0) :
    diagonalDilation ((diagonalWeight m - 1)⁻¹ • secularMode m)
      - (diagonalWeight m - 1)⁻¹ • secularMode m = secularMode m := by
  have hw : diagonalWeight m - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h => hm ((diagonalWeight_eq_one_iff m).mp h)
  rw [map_smul, diagonalDilation_mode, smul_smul, ← sub_smul]
  have hcoef : (diagonalWeight m - 1)⁻¹ * diagonalWeight m - (diagonalWeight m - 1)⁻¹
      = 1 := by
    field_simp
  rw [hcoef, one_smul]

/-- **Equivariant extractions are blind to the combination modes.**  A linear
map intertwining the single diagonal dilation annihilates every nonzero
combination mode: the nontrivial-weight lanes are invisible to any equivariant
extraction. -/
theorem diagonal_equivariant_kills_mode {N : Type*} [AddCommGroup N] [Module ℂ N]
    (r : SecularAlgebra →ₗ[ℂ] N) (hr : ∀ x, r (diagonalDilation x) = r x)
    {m : PrimeExponents} (hm : m ≠ 0) : r (secularMode m) = 0 :=
  equivariant_linear_kills_scaled r diagonalDilation hr (diagonalDilation_mode m)
    (fun h => hm ((diagonalWeight_eq_one_iff m).mp h))

/-- **No retraction equivariant for the diagonal dilation.**  Equivariance under
the single diagonal endomorphism already forbids an algebra retraction onto the
scalar block: a nonzero mode is a unit, and an equivariant retraction would
send it to `0`. -/
theorem no_diagonal_equivariant_retraction (r : SecularAlgebra →ₐ[ℂ] ℂ) :
    r.comp diagonalDilation ≠ r := by
  intro h
  have hm0 : (Finsupp.single (⟨2, Nat.prime_two⟩ : Nat.Primes) (1 : ℤ)) ≠ 0 :=
    Finsupp.single_ne_zero.mpr one_ne_zero
  have h0 : r (secularMode (Finsupp.single ⟨2, Nat.prime_two⟩ 1)) = 0 :=
    diagonal_equivariant_kills_mode r.toLinearMap
      (fun x => by simpa using DFunLike.congr_fun h x) hm0
  have h1 : r (secularMode (Finsupp.single ⟨2, Nat.prime_two⟩ 1))
      * r (secularMode (-(Finsupp.single ⟨2, Nat.prime_two⟩ 1))) = 1 := by
    rw [← map_mul, secularMode_mul_neg, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

end

end SecularWeld

end GaloisForLFunctions
