import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.HTGeometry.MixtureLogConcavity

/-!
# Log-slope and log-curvature of the theta atoms, in the mixture normal form

`MixtureLogConcavity` bounds the log-curvature of a finite mixture `Φ = ∑ φ_j` in terms of data
`a j`, `c j` satisfying

```text
φ_j′ = a j · φ_j ,        φ_j″ = (a j² − c j) · φ_j .
```

For the theta source those data already exist in the tree in Born–Witten form: the logarithmic score
of the `n`th atom is `−2 B_n` and the derivative of `B_n` is the Born–Witten curvature, so

```text
a n x = −2 · thetaCuspBornWittenSuperpotential n x ,
c n x =  2 · thetaCuspBornWittenCurvature n x .
```

This file records those identifications and the curvature floor in the form the mixture bound
consumes:

```text
c n x  ≥  4π n² e^{2x}      for n ≥ 1 and x ≥ 0 ,
```

which is the term-by-term half of the log-concavity of the theta kernel.  The remaining half — that
the weighted variance of the log-slopes stays below this floor — is a separate estimate and is not
proved here.
-/

open Real Set

namespace RHTower

noncomputable section

/-- Logarithmic score of the `n`th theta atom: `(log φ_n)′ = −2 B_n`. -/
def thetaCuspAtomLogSlope (n : ℕ) (x : ℝ) : ℝ :=
  -2 * thetaCuspBornWittenSuperpotential n x

/-- Logarithmic curvature of the `n`th theta atom: `−(log φ_n)″ = 2 · (Born–Witten curvature)`. -/
def thetaCuspAtomLogCurvature (n : ℕ) (x : ℝ) : ℝ :=
  2 * thetaCuspBornWittenCurvature n x

/-- The first mixture datum: the atom's derivative is its log-slope times itself. -/
theorem hasDerivAt_thetaCuspSourceTerm_logSlope
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => thetaCuspSourceTerm y n)
      (thetaCuspAtomLogSlope n x * thetaCuspSourceTerm x n) x := by
  have h := hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hn hx
  refine h.congr_deriv ?_
  unfold thetaCuspAtomLogSlope
  ring

/-- The log-slope is differentiable with derivative the negative of the log-curvature. -/
theorem hasDerivAt_thetaCuspAtomLogSlope
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspAtomLogSlope n) (-thetaCuspAtomLogCurvature n x) x := by
  have h := (hasDerivAt_thetaCuspBornWittenSuperpotential hn hx).const_mul (-2 : ℝ)
  refine h.congr_deriv ?_
  unfold thetaCuspAtomLogCurvature
  ring

/-- **The second mixture datum.**  The atom satisfies `φ″ = (a² − c)·φ`, the normal form the mixture
curvature identity consumes. -/
theorem hasDerivAt_thetaCuspSourceTerm_second
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => thetaCuspAtomLogSlope n y * thetaCuspSourceTerm y n)
      ((thetaCuspAtomLogSlope n x ^ 2 - thetaCuspAtomLogCurvature n x)
        * thetaCuspSourceTerm x n) x := by
  have hslope := hasDerivAt_thetaCuspAtomLogSlope hn hx.le
  have hsrc := hasDerivAt_thetaCuspSourceTerm_logSlope hn hx
  have h := hslope.mul hsrc
  refine h.congr_deriv ?_
  ring

/-- The Born–Witten curvature dominates twice the Morse scale: the correction term is nonnegative. -/
theorem two_mul_thetaCuspMorseScale_le_curvature
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspMorseScale n x ≤ thetaCuspBornWittenCurvature n x := by
  have hqpos := thetaCuspBornWittenWeight_pos hn hx
  have hscaleNonneg : 0 ≤ thetaCuspMorseScale n x := by
    simp only [thetaCuspMorseScale]; positivity
  have hcorr : 0 ≤ 3 * thetaCuspMorseScale n x / thetaCuspBornWittenWeight n x ^ 2 := by
    positivity
  simp only [thetaCuspBornWittenCurvature]
  linarith

/-- **The log-curvature floor for a theta atom.**  On the closed half-line every atom is log-concave
with curvature at least `4π n² e^{2x}` — the exact leading term, with the Born–Witten correction
discarded. -/
theorem thetaCuspAtomLogCurvature_floor
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) ≤ thetaCuspAtomLogCurvature n x := by
  have hscale : thetaCuspMorseScale n x = Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) := by
    simp only [thetaCuspMorseScale]
    rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
    ring
  have h := two_mul_thetaCuspMorseScale_le_curvature hn hx
  rw [hscale] at h
  unfold thetaCuspAtomLogCurvature
  linarith

/-- **Uniform floor over a family of atoms.**  Every atom of positive index has log-curvature at
least `4π e^{2x}`, so the constant `C` of `MixtureLogConcavity.mixture_curvature_ge` may be taken to
be `4π e^{2x}` for any finite set of positive indices. -/
theorem thetaCuspAtomLogCurvature_uniform_floor
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    4 * Real.pi * Real.exp (2 * x) ≤ thetaCuspAtomLogCurvature n x := by
  have hfloor := thetaCuspAtomLogCurvature_floor hn hx
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hexp : (0 : ℝ) < Real.exp (2 * x) := Real.exp_pos _
  have hgap : 0 ≤ 4 * Real.pi * Real.exp (2 * x) * ((n : ℝ) ^ 2 - 1) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hsq)
  nlinarith [hfloor, hgap]

/-- **The mixture bound, instantiated at the theta atoms.**  For any finite set `F` of positive atom
indices, the truncated theta source has log-curvature at least `4π e^{2x} − E`, where `E` is any
bound on the weighted variance of the atom log-slopes.  This discharges the curvature hypothesis of
`MixtureLogConcavity.mixture_curvature_ge` against the actual theta source; only the variance
hypothesis remains. -/
theorem thetaCuspTruncated_logCurvature_ge
    (F : Finset ℕ) (hF : ∀ n ∈ F, 0 < n) {x : ℝ} (hx : 0 < x) {E : ℝ}
    (hE : (∑ j ∈ F, ∑ k ∈ F, thetaCuspSourceTerm x j * thetaCuspSourceTerm x k
            * (thetaCuspAtomLogSlope j x - thetaCuspAtomLogSlope k x) ^ 2)
          ≤ 2 * E * (∑ j ∈ F, thetaCuspSourceTerm x j) ^ 2) :
    (4 * Real.pi * Real.exp (2 * x) - E) * (∑ j ∈ F, thetaCuspSourceTerm x j) ^ 2
      ≤ (∑ j ∈ F, thetaCuspAtomLogSlope j x * thetaCuspSourceTerm x j) ^ 2
        - (∑ j ∈ F, thetaCuspSourceTerm x j)
          * (∑ k ∈ F, (thetaCuspAtomLogSlope k x ^ 2 - thetaCuspAtomLogCurvature k x)
              * thetaCuspSourceTerm x k) := by
  refine GaloisForLFunctions.MixtureLogConcavity.mixture_curvature_ge F
    (fun j => thetaCuspSourceTerm x j) (fun j => thetaCuspAtomLogSlope j x)
    (fun j => thetaCuspAtomLogCurvature j x) ?_ ?_ hE
  · intro j hj
    exact (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (hF j hj)).le
  · intro j hj
    exact thetaCuspAtomLogCurvature_uniform_floor (hF j hj) hx.le


/-! ### The log-slope gap is Lipschitz in the Morse scale

The corpus already proves the exact superpotential difference

```text
B_n − B_m = (scale_n − scale_m)·(1 + (3/2)/(w_n w_m)) ,      w = scale − 3/2 ,
```

so the log-slope gap is `−2` times that.  On `x ≥ 0` with positive indices every `w` is at least
`π − 3/2`, so the bracket is bounded and the gap is Lipschitz in the scale gap with an explicit
constant.  This reduces the weighted log-slope variance — the one hypothesis left in
`thetaCuspTruncated_logCurvature_ge` — to the weighted variance of the Morse scales, i.e. of the
squared atom indices. -/

/-- The explicit Lipschitz constant of the log-slope gap against the Morse-scale gap on `x ≥ 0`. -/
def logSlopeLipschitz : ℝ := 2 + 3 / (Real.pi - 3 / 2) ^ 2

theorem logSlopeLipschitz_pos : 0 < logSlopeLipschitz := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  unfold logSlopeLipschitz
  have : (0 : ℝ) < Real.pi - 3 / 2 := by linarith
  positivity

/-- Every positive-index Morse scale is at least `π` on the closed half-line. -/
theorem pi_le_thetaCuspMorseScale {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    Real.pi ≤ thetaCuspMorseScale n x := by
  have h := thetaCuspMorseScale_pi_mul_sq_le (n := n) hx
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  nlinarith [Real.pi_pos, h, hsq]

/-- The Born–Witten weight is at least `π − 3/2` on the closed half-line. -/
theorem pi_sub_le_thetaCuspBornWittenWeight {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    Real.pi - 3 / 2 ≤ thetaCuspBornWittenWeight n x := by
  rw [thetaCuspBornWittenWeight_eq]
  linarith [pi_le_thetaCuspMorseScale hn hx]

/-- **The log-slope gap in exact form.** -/
theorem thetaCuspAtomLogSlope_sub_eq
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspAtomLogSlope n x - thetaCuspAtomLogSlope m x
      = -2 * (thetaCuspMorseScale n x - thetaCuspMorseScale m x)
        * (1 + (3 / 2 : ℝ) /
            (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x)) := by
  unfold thetaCuspAtomLogSlope
  rw [show (-2 : ℝ) * thetaCuspBornWittenSuperpotential n x
      - -2 * thetaCuspBornWittenSuperpotential m x
      = -2 * (thetaCuspBornWittenSuperpotential n x
          - thetaCuspBornWittenSuperpotential m x) by ring,
    thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul hm hn hx]
  ring

/-- **The log-slope gap is Lipschitz in the Morse-scale gap**, with the explicit constant
`2 + 3/(π − 3/2)²`. -/
theorem thetaCuspAtomLogSlope_sub_sq_le
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (thetaCuspAtomLogSlope n x - thetaCuspAtomLogSlope m x) ^ 2
      ≤ logSlopeLipschitz ^ 2
        * (thetaCuspMorseScale n x - thetaCuspMorseScale m x) ^ 2 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hp : (0 : ℝ) < Real.pi - 3 / 2 := by linarith
  have hwn := pi_sub_le_thetaCuspBornWittenWeight hn hx
  have hwm := pi_sub_le_thetaCuspBornWittenWeight hm hx
  have hprod : (Real.pi - 3 / 2) ^ 2
      ≤ thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x := by
    nlinarith [hwn, hwm, hp]
  have hprodpos : (0 : ℝ) < thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x := by
    nlinarith [hwn, hwm, hp]
  have hfrac : (3 / 2 : ℝ) /
      (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x)
      ≤ (3 / 2 : ℝ) / (Real.pi - 3 / 2) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod
  have hbrk : (0 : ℝ) ≤ 1 + (3 / 2 : ℝ) /
      (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x) := by positivity
  have hbrk2 : 2 * (1 + (3 / 2 : ℝ) /
      (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x)) ≤ logSlopeLipschitz := by
    unfold logSlopeLipschitz
    have : (3 : ℝ) / (Real.pi - 3 / 2) ^ 2 = 2 * ((3 / 2 : ℝ) / (Real.pi - 3 / 2) ^ 2) := by
      ring
    rw [this]
    linarith [hfrac]
  rw [thetaCuspAtomLogSlope_sub_eq hm hn hx]
  set B : ℝ := 1 + (3 / 2 : ℝ) /
    (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x) with hBdef
  set D : ℝ := thetaCuspMorseScale n x - thetaCuspMorseScale m x with hDdef
  have hu : (0 : ℝ) ≤ 2 * B := by linarith [hbrk]
  have husq : (2 * B) ^ 2 ≤ logSlopeLipschitz ^ 2 := by nlinarith [hu, hbrk2]
  calc (-2 * D * B) ^ 2 = (2 * B) ^ 2 * D ^ 2 := by ring
    _ ≤ logSlopeLipschitz ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_right husq (sq_nonneg D)

/-- **The weighted log-slope variance is controlled by the weighted Morse-scale variance.**  This is
the analytic half of the hypothesis `hE` of `thetaCuspTruncated_logCurvature_ge`: what remains is a
purely combinatorial quantity, the weighted variance of the squared atom indices. -/
theorem thetaCuspLogSlopeVariance_le
    (F : Finset ℕ) (hF : ∀ n ∈ F, 0 < n) {x : ℝ} (hx : 0 < x) :
    (∑ j ∈ F, ∑ k ∈ F, thetaCuspSourceTerm x j * thetaCuspSourceTerm x k
        * (thetaCuspAtomLogSlope j x - thetaCuspAtomLogSlope k x) ^ 2)
      ≤ logSlopeLipschitz ^ 2 * ∑ j ∈ F, ∑ k ∈ F, thetaCuspSourceTerm x j
          * thetaCuspSourceTerm x k * (thetaCuspMorseScale j x - thetaCuspMorseScale k x) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hpj := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (hF j hj)).le
  have hpk := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (hF k hk)).le
  have hgap := thetaCuspAtomLogSlope_sub_sq_le (hF k hk) (hF j hj) hx.le
  have hmul : 0 ≤ thetaCuspSourceTerm x j * thetaCuspSourceTerm x k := mul_nonneg hpj hpk
  nlinarith [hgap, hmul]


/-! ### The atom ratio, in closed form and bounded

`Var_w(n²)` is what is left of the mixture hypothesis, and it is controlled by the atom ratios
`φ_n/φ_1`.  Those have a closed form in the Morse scale: with `s_n = thetaCuspMorseScale n x`,

```text
φ_n = e^{x/2}·2 s_n (2 s_n − 3) e^{−s_n} ,       s_n = n² s_1 ,
```

so

```text
φ_n/φ_1 = n²·( n² + 3(n²−1)/(2s_1 − 3) )·e^{−(n²−1)s_1}  ≤  2 n⁴ e^{−(n²−1)s_1} ,
```

the last step using only `s_1 ≥ 3`, which holds on `x ≥ 0` because `π > 3`. -/

/-- The atom in Morse coordinates: `φ_n = e^{x/2}·2 s_n(2 s_n − 3)e^{−s_n}`. -/
theorem thetaCuspSourceTerm_eq_morse (n : ℕ) (x : ℝ) :
    thetaCuspSourceTerm x n
      = Real.exp (x / 2) * (2 * thetaCuspMorseScale n x
          * (2 * thetaCuspMorseScale n x - 3)
          * Real.exp (-thetaCuspMorseScale n x)) := by
  unfold thetaCuspSourceTerm thetaCuspSeed thetaCuspMorseScale
  rw [show -Real.pi * ((n : ℝ) * Real.exp x) ^ 2
      = -(Real.pi * ((n : ℝ) * Real.exp x) ^ 2) by ring]
  ring

/-- The Morse scale is quadratic in the atom index. -/
theorem thetaCuspMorseScale_eq_sq_mul (n : ℕ) (x : ℝ) :
    thetaCuspMorseScale n x = (n : ℝ) ^ 2 * thetaCuspMorseScale 1 x := by
  unfold thetaCuspMorseScale
  push_cast
  ring

/-- The algebraic core of the ratio bound: for `s ≥ 3` and `m ≥ 1`,
`2(ms)(2ms − 3) ≤ 2m²·2s(2s − 3)`. -/
theorem morse_ratio_algebra {s m : ℝ} (hs : 3 ≤ s) (hm : 1 ≤ m) :
    2 * (m * s) * (2 * (m * s) - 3) ≤ 2 * m ^ 2 * (2 * s * (2 * s - 3)) := by
  have hspos : (0 : ℝ) < s := by linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hstep : 6 * m - 3 ≤ 2 * m * s := by nlinarith
  have hprod : 0 ≤ 2 * m * s * (2 * m * s - (6 * m - 3)) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [hprod]

/-- **The atom ratio bound.**  On the closed half-line, `φ_n ≤ 2n⁴e^{−(n²−1)s₁}·φ₁`. -/
theorem thetaCuspSourceTerm_le_ratio_bound
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x n
      ≤ 2 * (n : ℝ) ^ 4
        * Real.exp (-(((n : ℝ) ^ 2 - 1) * thetaCuspMorseScale 1 x))
        * thetaCuspSourceTerm x 1 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs1 : (3 : ℝ) ≤ thetaCuspMorseScale 1 x := by
    have := pi_le_thetaCuspMorseScale (n := 1) one_pos hx
    linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have halg := morse_ratio_algebra hs1 hnsq
  have hexp : Real.exp (-thetaCuspMorseScale n x)
      = Real.exp (-(((n : ℝ) ^ 2 - 1) * thetaCuspMorseScale 1 x))
        * Real.exp (-thetaCuspMorseScale 1 x) := by
    rw [← Real.exp_add, thetaCuspMorseScale_eq_sq_mul n x]
    congr 1
    ring
  rw [thetaCuspSourceTerm_eq_morse n x, thetaCuspSourceTerm_eq_morse 1 x, hexp,
    thetaCuspMorseScale_eq_sq_mul n x]
  have hE : (0 : ℝ) < Real.exp (-(((n : ℝ) ^ 2 - 1) * thetaCuspMorseScale 1 x)) :=
    Real.exp_pos _
  have hE2 : (0 : ℝ) < Real.exp (-thetaCuspMorseScale 1 x) := Real.exp_pos _
  have hX : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have hfac : (0 : ℝ) ≤ Real.exp (x / 2)
      * (Real.exp (-(((n : ℝ) ^ 2 - 1) * thetaCuspMorseScale 1 x))
        * Real.exp (-thetaCuspMorseScale 1 x)) := by positivity
  nlinarith [halg, hfac]

end

end RHTower
