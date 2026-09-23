/-
Exponent arithmetic of a bound for divisor sums against a `k`-th-root phase.

For `G_k(y) = Σ_{m≤y} d_k(m) e(k y^{1/k} m^{1/k})` the Mellin representation is
`G_k(y) = (1/2πi)∫ζ(s)^k M(s)ds` with `M(s) = k∫_1^V v^{ks-1}e(kXv)dv`, `X = V = y^{1/k}`.
Stationary phase gives `|M| ≍ √k · v₀^{(k-1)/2}/√X` at `v₀ = |t|/(2πX)`, supported on `|t| ≤ 2πXV`,
so the mass sits at `T = XV = y^{2/k}`.

Hölder against the fourth moment of `ζ` (exponents `4/k` and `4/(4-k)`, valid for `k < 4`, and by
continuity at `k = 4`) yields

    |G_k(y)| ≪ (∫_{|t|≍T}|ζ|^(4 : ℕ))^{k/4} · (∫|M|^{q})^{1/q},   q = 4/(4-k),

and the two exponents combine to `1/2 + 1/k`.  The same computation with the sixth moment
(`m(3) ≤ 5/4`) covers `4 < k < 6` and gives `5/12 + (k+6)/(6k)`.
-/
import GaloisForLFunctions.HTGeometry.MomentChordPivot

namespace HTGeometry

/-- Exponent delivered by Hölder against the fourth moment: `1/2 + 1/k`. -/
def fourthMomentPhaseExponent (k : ℚ) : ℚ := 1/2 + 1/k

@[simp] theorem fourthMomentPhaseExponent_three : fourthMomentPhaseExponent 3 = 5/6 := by
  unfold fourthMomentPhaseExponent; norm_num

@[simp] theorem fourthMomentPhaseExponent_four : fourthMomentPhaseExponent 4 = 3/4 := by
  unfold fourthMomentPhaseExponent; norm_num

/-- At `k = 2` the exponent is `1` — the method gives exactly nothing, as it must, since the
stationary-phase mass and the trivial bound coincide there. -/
@[simp] theorem fourthMomentPhaseExponent_two : fourthMomentPhaseExponent 2 = 1 := by
  unfold fourthMomentPhaseExponent; norm_num

/-- **Nontrivial exactly for `k > 2`.** -/
theorem fourthMomentPhaseExponent_lt_one {k : ℚ} (hk : 0 < k) :
    fourthMomentPhaseExponent k < 1 ↔ 2 < k := by
  unfold fourthMomentPhaseExponent
  constructor
  · intro h
    have : (1:ℚ)/k < 1/2 := by linarith
    rw [div_lt_div_iff₀ hk (by norm_num)] at this
    linarith
  · intro h
    have : (1:ℚ)/k < 1/2 := by
      rw [div_lt_div_iff₀ hk (by norm_num)]; linarith
    linarith

/-- The exponent decreases in `k`: higher divisor functions get better savings from the same
fourth-moment input. -/
theorem fourthMomentPhaseExponent_strictAnti {k l : ℚ} (hk : 0 < k) (hkl : k < l) :
    fourthMomentPhaseExponent l < fourthMomentPhaseExponent k := by
  unfold fourthMomentPhaseExponent
  have hl : (0:ℚ) < l := lt_trans hk hkl
  have : (1:ℚ)/l < 1/k := by rw [div_lt_div_iff₀ hl hk]; linarith
  linarith

/-- Exponent delivered by Hölder against the sixth moment with `m(3) ≤ 5/4`, valid for `4 < k < 6`. -/
def sixthMomentPhaseExponent (k : ℚ) : ℚ := 5/12 + (k + 6) / (6 * k)

@[simp] theorem sixthMomentPhaseExponent_five : sixthMomentPhaseExponent 5 = 47/60 := by
  unfold sixthMomentPhaseExponent; norm_num

/-- At `k = 4` the fourth-moment route is strictly better, so the crossover is above `4`. -/
theorem fourth_beats_sixth_at_four :
    fourthMomentPhaseExponent 4 < sixthMomentPhaseExponent 4 := by
  rw [fourthMomentPhaseExponent_four]
  unfold sixthMomentPhaseExponent; norm_num

/-- What the best known exponent pair gives for the same sum: `κ+λ ≤ 1 − kη` with Bourgain's
`κ+λ = 17/21`, i.e. `η ≤ 4/(21k)`. -/
def exponentPairPhaseExponent (k : ℚ) : ℚ := 1 - 4 / (21 * k)

/-- **The fourth-moment route beats the best exponent pair exactly for `k > 50/21 = 2.38…`.**  In
particular at every integer `k ≥ 3`.  (The two coincide at `k = 50/21`; below it the exponent pair is
better, but there the fourth-moment exponent is already close to trivial.) -/
theorem fourthMoment_beats_exponentPair {k : ℚ} (hk : 50/21 < k) :
    fourthMomentPhaseExponent k < exponentPairPhaseExponent k := by
  have hk0 : (0:ℚ) < k := by linarith
  unfold fourthMomentPhaseExponent exponentPairPhaseExponent
  rw [← sub_pos]
  have h1 : (1:ℚ) - 4/(21*k) - (1/2 + 1/k) = 1/2 - 25/(21*k) := by
    field_simp; ring
  rw [h1, sub_pos, div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

@[simp] theorem exponentPairPhaseExponent_three : exponentPairPhaseExponent 3 = 59/63 := by
  unfold exponentPairPhaseExponent; norm_num

end HTGeometry
