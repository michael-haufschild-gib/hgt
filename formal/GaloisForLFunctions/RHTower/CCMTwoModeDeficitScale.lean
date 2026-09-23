import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The zero-integral two-mode source and its central value

A two-mode concentration source is normalised so that its total integral vanishes:

```text
g = (l1 e0 - l0 e1) / sqrt (l0^(2 : ℕ) + l1^(2 : ℕ)),   l_j = c_j e_j(0),
```

where `c_j` are the concentration eigenvalues and `l_j` the total integrals of the modes.  Two facts
about its value at the origin are proved here.

* `twoModeSource_eq_of_eigen` — an exact algebraic identity: the eigen-relation `l_j = c_j e_j(0)`
  turns the value at the origin into `l0 l1 (c1 - c0) / (c0 c1 sqrt(l0^(2 : ℕ) + l1^(2 : ℕ)))`.  The **difference**
  of the eigenvalues appears; that is the first-order cancellation created by the zero-integral
  combination.
* `tendsto_twoModeSource_div_deficit` — consequently, with the fixed-mode asymptotics as hypotheses,
  the value is of concentration-deficit order `d1 = 1 - c1^(2 : ℕ)`, not of square-root-leakage order
  `sqrt d1`, and the limiting ratio is the explicit constant `-2^{-3/4} sqrt(3/11)`.

The asymptotics themselves are inputs, stated as `Tendsto` hypotheses; everything derived from them is
unconditional.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-- The value at the origin of the normalised zero-integral two-mode source. -/
def twoModeSource (l0 l1 e0 e1 : ℝ) : ℝ := (l1 * e0 - l0 * e1) / Real.sqrt (l0 ^ 2 + l1 ^ 2)

/-- **The central value of the zero-integral combination.**  Under the eigen-relation `l_j = c_j e_j`
the value at the origin is proportional to the *difference* `c1 - c0` of the concentration
eigenvalues.  No asymptotics are used: this is an identity. -/
theorem twoModeSource_eq_of_eigen {l0 l1 c0 c1 e0 e1 : ℝ}
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) (h0 : l0 = c0 * e0) (h1 : l1 = c1 * e1) :
    twoModeSource l0 l1 e0 e1
      = l0 * l1 * (c1 - c0) / (c0 * c1 * Real.sqrt (l0 ^ 2 + l1 ^ 2)) := by
  rw [twoModeSource]
  rcases eq_or_ne (Real.sqrt (l0 ^ 2 + l1 ^ 2)) 0 with hd | hd
  · rw [hd]
    simp
  · rw [h0, h1]
    field_simp

/-- A vanishing concentration deficit forces the eigenvalue to one. -/
theorem tendsto_one_of_tendsto_deficit {ι : Type*} {L : Filter ι} {c d : ι → ℝ}
    (hd : ∀ i, d i = 1 - c i ^ 2) (hc : ∀ i, 0 ≤ c i) (h : Tendsto d L (𝓝 0)) :
    Tendsto c L (𝓝 1) := by
  have hrw : ∀ i, c i = Real.sqrt (1 - d i) := by
    intro i
    rw [hd i, sub_sub_cancel, Real.sqrt_sq (hc i)]
  have hlim : Tendsto (fun i => 1 - d i) L (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := L)).sub h
  have := hlim.sqrt
  rw [Real.sqrt_one] at this
  exact this.congr fun i => (hrw i).symm

/-- The limiting ratio of the two-mode central value to the concentration deficit. -/
theorem deficitScale_const :
    ((2 : ℝ) ^ ((1 : ℝ) / 4) * (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))
        / (1 * 1 * Real.sqrt (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2
            + (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2))
        * (-(1 / 2) : ℝ)
      = -((2 : ℝ) ^ (-(3 : ℝ) / 4) * Real.sqrt (3 / 11)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  set s : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) with hsdef
  have hspos : 0 < s := Real.rpow_pos_of_pos h2 _
  have hs4 : s ^ 4 = 2 := by
    rw [hsdef, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul h2.le]
    norm_num
  have h54 : (2 : ℝ) ^ ((5 : ℝ) / 4) = 2 * s := by
    rw [hsdef, show (5 : ℝ) / 4 = 1 + (1 : ℝ) / 4 by ring, Real.rpow_add h2, Real.rpow_one]
  have h34 : (2 : ℝ) ^ (-(3 : ℝ) / 4) = s / 2 := by
    rw [hsdef, show -(3 : ℝ) / 4 = (1 : ℝ) / 4 - 1 by ring, Real.rpow_sub h2, Real.rpow_one]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h11pos : 0 < Real.sqrt 11 := Real.sqrt_pos.mpr (by norm_num)
  have hsum : s ^ 2 + (Real.sqrt 3 / (2 * s)) ^ 2 = 11 / (4 * s ^ 2) := by
    rw [div_pow, h3]
    field_simp
    nlinarith [hs4]
  have hsqrt : Real.sqrt (11 / (4 * s ^ 2)) = Real.sqrt 11 / (2 * s) := by
    rw [show (11 : ℝ) / (4 * s ^ 2) = (Real.sqrt 11 / (2 * s)) ^ 2 from by
      rw [div_pow, h11]; ring]
    exact Real.sqrt_sq (by positivity)
  have h311 : Real.sqrt (3 / 11) = Real.sqrt 3 / Real.sqrt 11 :=
    Real.sqrt_div (by norm_num) 11
  rw [h54, h34, h311, hsum, hsqrt]
  field_simp

/-- **The central correction is of deficit order.**  With the fixed-mode prolate asymptotics as
hypotheses — both deficits vanish, the two total integrals converge to their limits, and the
eigenvalue gap is asymptotically half the second deficit — the two-mode central value divided by the
deficit converges to `-2^{-3/4} sqrt(3/11)`.

The point of the statement is the *scale*: the ratio has a finite nonzero limit against `d1`, so the
zero-mode Poisson correction is of concentration-deficit order and not of square-root-leakage
order. -/
theorem tendsto_twoModeSource_div_deficit {ι : Type*} {L : Filter ι}
    {l0 l1 c0 c1 d0 d1 G : ι → ℝ}
    (hd0 : ∀ i, d0 i = 1 - c0 i ^ 2) (hd1 : ∀ i, d1 i = 1 - c1 i ^ 2)
    (hc0nn : ∀ i, 0 ≤ c0 i) (hc1nn : ∀ i, 0 ≤ c1 i)
    (hd0lim : Tendsto d0 L (𝓝 0)) (hd1lim : Tendsto d1 L (𝓝 0))
    (hl0 : Tendsto l0 L (𝓝 ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto l1 L (𝓝 (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))))
    (hgap : Tendsto (fun i => (c0 i - c1 i) / d1 i) L (𝓝 (1 / 2)))
    (hG : ∀ i, G i
      = l0 i * l1 i * (c1 i - c0 i) / (c0 i * c1 i * Real.sqrt (l0 i ^ 2 + l1 i ^ 2))) :
    Tendsto (fun i => G i / d1 i) L (𝓝 (-((2 : ℝ) ^ (-(3 : ℝ) / 4) * Real.sqrt (3 / 11)))) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  set L0 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) with hL0
  set L1 : ℝ := Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) with hL1
  have hL0pos : 0 < L0 := Real.rpow_pos_of_pos h2 _
  have hdenpos : 0 < 1 * 1 * Real.sqrt (L0 ^ 2 + L1 ^ 2) := by
    have : 0 < L0 ^ 2 + L1 ^ 2 := by positivity
    simpa using Real.sqrt_pos.mpr this
  have hc0lim : Tendsto c0 L (𝓝 1) := tendsto_one_of_tendsto_deficit hd0 hc0nn hd0lim
  have hc1lim : Tendsto c1 L (𝓝 1) := tendsto_one_of_tendsto_deficit hd1 hc1nn hd1lim
  have hsqlim : Tendsto (fun i => Real.sqrt (l0 i ^ 2 + l1 i ^ 2)) L
      (𝓝 (Real.sqrt (L0 ^ 2 + L1 ^ 2))) := ((hl0.pow 2).add (hl1.pow 2)).sqrt
  have hfac : Tendsto (fun i => l0 i * l1 i / (c0 i * c1 i * Real.sqrt (l0 i ^ 2 + l1 i ^ 2))) L
      (𝓝 (L0 * L1 / (1 * 1 * Real.sqrt (L0 ^ 2 + L1 ^ 2)))) :=
    (hl0.mul hl1).div ((hc0lim.mul hc1lim).mul hsqlim) (ne_of_gt hdenpos)
  have hprod := hfac.mul hgap.neg
  have hval : L0 * L1 / (1 * 1 * Real.sqrt (L0 ^ 2 + L1 ^ 2)) * (-(1 / 2))
      = -((2 : ℝ) ^ (-(3 : ℝ) / 4) * Real.sqrt (3 / 11)) := by
    rw [hL0, hL1]
    exact deficitScale_const
  rw [hval] at hprod
  refine hprod.congr fun i => ?_
  rw [hG i]
  ring

end GaloisForLFunctions.RHTower

end
