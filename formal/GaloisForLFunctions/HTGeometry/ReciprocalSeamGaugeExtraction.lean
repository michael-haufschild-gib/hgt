import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Canonical seam extraction and the zero-free even gauge counterterm

The reciprocal seam moments are read from the completed logarithmic derivative by the monomial
extractor `h_k(w) = 2(-1)^k w^{-2k}`, taking the Hadamard finite part in the even seam sense.  For
an odd germ

`L(w) = Σ_{n ≥ 0} ℓ_n w^{2n+1}`

only one term of `h_k · L` can carry a `w^{-1}`, namely `n = k - 1`, because `2n + 1 - 2k = -1` has
that unique solution.  Two consequences:

* on the canonical divisor expansion `ℓ_n = (-1)^n T_{n+1}` the extractor returns exactly `T_k`;
* a zero-free even gauge `F ↦ exp(q(w²)) F` adds the odd germ `d/dw q(w²) = Σ_r 2 r a_r w^{2r-1}`,
  whose only contributing term is `r = k`, so the extractor shifts by exactly `2k(-1)^{k+1} a_k`.

The induced change of the shifted `Q₀` Hankel tower depends only on `i + j`, hence is itself Hankel:
a zero-free multiplier moves no zero, and its whole effect on the seam tower is this local Hankel
counterterm.

## Main results

* `seamContributes_iff` — the residue occurs only at `n = k - 1`;
* `seamExtract_canonical` — `E_k` on the canonical expansion is `T_k`;
* `seamExtract_gaugeGerm` — the gauge shift is `2k(-1)^{k+1} a_k`;
* `logDeriv_evenGauge` — the analytic gauge law `(e^{q}F)'/(e^{q}F) = q' + F'/F`;
* `seamExtract_gauged`, `gaugeHankelCounterterm_isHankel` — the counterterm and its Hankel shape.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-! ### The residue selection -/

/-- The `w`-exponent of the `n`-th term of `h_k(w) · L(w)` for an odd germ `L`. -/
def seamTermExponent (k n : ℕ) : ℤ := 2 * (n : ℤ) + 1 - 2 * (k : ℤ)

/-- **Only one term contributes a residue.**  For `k ≥ 1` the exponent equation
`2n + 1 - 2k = -1` holds exactly at `n = k - 1`. -/
theorem seamContributes_iff {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    seamTermExponent k n = -1 ↔ n = k - 1 := by
  unfold seamTermExponent
  constructor
  · intro h
    omega
  · intro h
    subst h
    have : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
    omega

/-- The seam extractor applied to the odd germ with coefficient sequence `l`:
`E_k = -(1/2) · [w^{-1}] (2(-1)^k w^{-2k} · Σ_n l n w^{2n+1})`. -/
def seamExtract (k : ℕ) (l : ℕ → ℝ) : ℝ := -((-1 : ℝ) ^ k) * l (k - 1)

theorem seamExtract_add (k : ℕ) (l g : ℕ → ℝ) :
    seamExtract k (l + g) = seamExtract k l + seamExtract k g := by
  unfold seamExtract
  simp only [Pi.add_apply]
  ring

/-! ### The canonical extraction -/

/-- The canonical divisor expansion `Xi'/Xi = Σ_n (-1)^n T_{n+1} w^{2n+1}`. -/
def canonicalSeamGerm (T : ℕ → ℝ) : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * T (n + 1)

/-- **Canonical extraction.**  On the canonical divisor expansion the extractor returns the folded
reciprocal moment. -/
theorem seamExtract_canonical (T : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    seamExtract k (canonicalSeamGerm T) = T k := by
  unfold seamExtract canonicalSeamGerm
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1]
  have hpow : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k - 1) = -1 := by
    rw [← pow_add]
    have hodd : Odd (k + (k - 1)) := by
      refine ⟨k - 1, by omega⟩
    exact hodd.neg_one_pow
  calc -((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ (k - 1) * T k)
      = -((-1 : ℝ) ^ k * (-1 : ℝ) ^ (k - 1)) * T k := by ring
    _ = T k := by rw [hpow]; ring

/-! ### The gauge germ -/

/-- The odd germ contributed by a zero-free even gauge `exp(q(w²))` with
`q(w²) = Σ_{r ≥ 1} a_r w^{2r}`: its derivative is `Σ_r 2 r a_r w^{2r-1}`, whose coefficient at
`w^{2n+1}` is `2(n+1) a_{n+1}`. -/
def gaugeSeamGerm (a : ℕ → ℝ) : ℕ → ℝ := fun n => 2 * ((n : ℝ) + 1) * a (n + 1)

/-- **The gauge shift.**  The extractor changes by exactly `2k(-1)^{k+1} a_k`. -/
theorem seamExtract_gaugeGerm (a : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    seamExtract k (gaugeSeamGerm a) = 2 * (k : ℝ) * (-1 : ℝ) ^ (k + 1) * a k := by
  unfold seamExtract gaugeSeamGerm
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1]
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have : (k - 1 : ℕ) = k - 1 := rfl
      push_cast [Nat.cast_sub hk]
      ring
    rw [this]
    ring
  rw [hcast]
  have hpow : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by
    rw [pow_succ]
    ring
  rw [hpow]
  ring

/-- **The gauged extraction.**  A zero-free even gauge shifts every seam moment by the explicit
local counterterm and by nothing else. -/
theorem seamExtract_gauged (T a : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    seamExtract k (canonicalSeamGerm T + gaugeSeamGerm a)
      = T k + 2 * (k : ℝ) * (-1 : ℝ) ^ (k + 1) * a k := by
  rw [seamExtract_add, seamExtract_canonical T hk, seamExtract_gaugeGerm a hk]

/-! ### The analytic gauge law -/

/-- **The analytic gauge law.**  Multiplying by a zero-free exponential adds the derivative of the
exponent to the logarithmic derivative. -/
theorem logDeriv_evenGauge {q F : ℂ → ℂ} {w : ℂ}
    (hq : DifferentiableAt ℂ q w) (hF : DifferentiableAt ℂ F w) (hFne : F w ≠ 0) :
    logDeriv (fun z => Complex.exp (q z) * F z) w = deriv q w + logDeriv F w := by
  have hexpne : Complex.exp (q w) ≠ 0 := Complex.exp_ne_zero _
  have hexpdiff : DifferentiableAt ℂ (fun z => Complex.exp (q z)) w :=
    (Complex.differentiable_exp.differentiableAt).comp w hq
  rw [logDeriv_mul w hexpne hFne hexpdiff hF]
  congr 1
  rw [logDeriv_apply, deriv_cexp hq]
  field_simp

/-! ### The Hankel counterterm -/

/-- The counterterm induced on the shifted `Q₀` tower `H_{ij} = T_{i+j+1}`. -/
def gaugeHankelCounterterm (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  2 * ((i + j : ℕ) + 1 : ℝ) * (-1 : ℝ) ^ (i + j + 2) * a (i + j + 1)

/-- **The counterterm is Hankel.**  It depends on `(i, j)` only through `i + j`. -/
theorem gaugeHankelCounterterm_isHankel (a : ℕ → ℝ) {i j i' j' : ℕ} (h : i + j = i' + j') :
    gaugeHankelCounterterm a i j = gaugeHankelCounterterm a i' j' := by
  unfold gaugeHankelCounterterm
  rw [h]

/-- The tower entry shifts by exactly the counterterm. -/
theorem shiftedTowerEntry_gauged (T a : ℕ → ℝ) (i j : ℕ) :
    seamExtract (i + j + 1) (canonicalSeamGerm T + gaugeSeamGerm a)
      = T (i + j + 1) + gaugeHankelCounterterm a i j := by
  rw [seamExtract_gauged T a (by omega)]
  unfold gaugeHankelCounterterm
  have hpow : (-1 : ℝ) ^ (i + j + 1 + 1) = (-1 : ℝ) ^ (i + j + 2) := by
    congr 1
  have hcast : ((i + j + 1 : ℕ) : ℝ) = ((i + j : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hpow, hcast]

end GaloisForLFunctions.HTGeometry
