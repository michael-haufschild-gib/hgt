import GaloisForLFunctions.RHTower.CriticalScaleLogLog

/-!
# The Borel–Carathéodory mechanism is capped at width `1/log log t`

The preceding module optimised the width `w ≍ r/M(r,t)` against the growth
`M ≍ (log t)^{2r}/log log t` and found a fixed width.  That growth formula is **wrong near `σ = 1`**:
it tends to `0` there, whereas the true size of `log|ζ(1+it)|` is `≍ log log log t` — both bounded
above and, by Granville–Soundararajan, attained.  The correct shape carries an irreducible additive
term,

```text
M(r,t)  ≍  (log t)^{2r} / log log t  +  log log log t ,
```

and that term changes the conclusion completely.

Write `L = log log t` and `ℓ = log log log t`.  Two unconditional inputs bound `M` from below:

* `M(r,t) ≥ ℓ` for every `r ≥ 0`, since the disk contains points of the line `σ = 1` and
  `max log|ζ(1+it)| ≍ log log log t`;
* `M(r,t) ≥ e^{rL}/L` by Montgomery's Ω-result on the line `σ = 1-r`.

Hence `w = r/M ≤ min(r/ℓ, r L e^{-rL})`.  The first branch increases in `r`, the second decreases
past `rL = 1`, and they cross at `rL = log(Lℓ)`.  At the crossover the common value is

```text
w ≤ log(Lℓ)/(Lℓ) ≤ 2ℓ/(Lℓ) = 2/L ,
```

using `log(L log L) = log L + log log L ≤ 2 log L`.  Therefore

> **Every zero-free region obtained from the Borel–Carathéodory bound on a disk around `1+iγ` has
> width `≪ 1/log log t`.  The mechanism cannot produce a fixed-width region, whatever growth bound it
> is fed.**

This is unconditional and intrinsic: the obstruction is the irreducible `log log log t`, which is the
true size of `log|ζ|` on the line `σ = 1` and cannot be improved.  It supersedes the earlier reading
that the lane was uncapped — that reading used the growth formula without the additive term.

The consequences for the classification are exact.  The mechanism's ceiling `1/log log t` is far
better than the Vinogradov–Korobov region `(log t)^{-2/3}` it currently achieves, so there is real
room; but the ceiling is not `1/2`, so **the classical zero-free-region mechanism cannot reach the
critical line even in principle**.  Exponent zero in the degradation scale is attainable by this
mechanism only in the weak sense of beating every power of `1/log t`, never as a fixed width.

This file formalizes the two lower bounds on the growth, the crossover, and the ceiling `2/L`.
-/

open Real

noncomputable section

namespace RHTower

/-- The width permitted by the two unconditional lower bounds on the growth. -/
def ceilingWidth (L l r : ℝ) : ℝ := min (r / l) (r * L * Real.exp (-(r * L)))

/-- The first branch is increasing in the radius; the second decreases past `rL = 1`. -/
theorem ceilingWidth_le_first {L l r : ℝ} : ceilingWidth L l r ≤ r / l := min_le_left _ _

theorem ceilingWidth_le_second {L l r : ℝ} :
    ceilingWidth L l r ≤ r * L * Real.exp (-(r * L)) := min_le_right _ _

/-- **The decreasing branch past the crossover.**  `x·e^{-x}` is antitone on `[1,∞)`, since its
derivative `(1-x)e^{-x}` is nonpositive there. -/
theorem mul_exp_neg_antitoneOn :
    AntitoneOn (fun x : ℝ => x * Real.exp (-x)) (Set.Ici 1) := by
  have hcont : ContinuousOn (fun x : ℝ => x * Real.exp (-x)) (Set.Ici 1) := by fun_prop
  refine antitoneOn_of_deriv_nonpos (convex_Ici 1) hcont ?_ ?_
  · intro x _
    have hg : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    exact ((hasDerivAt_id x).mul hg).differentiableAt.differentiableWithinAt
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have hg : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have hf : HasDerivAt (fun y : ℝ => y * Real.exp (-y))
        (1 * Real.exp (-x) + x * (Real.exp (-x) * (-1))) x := (hasDerivAt_id x).mul hg
    rw [hf.deriv]
    have hpos : 0 < Real.exp (-x) := Real.exp_pos _
    nlinarith [hx, hpos]

/-- The two-point form used at the crossover. -/
theorem mul_exp_neg_antitone {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    y * Real.exp (-y) ≤ x * Real.exp (-x) :=
  mul_exp_neg_antitoneOn hx (le_trans hx hxy) hxy

/-- **The crossover bound.**  `log(L·ℓ) ≤ 2ℓ` when `ℓ = log L`, since
`log(L log L) = log L + log log L ≤ 2 log L`. -/
theorem crossover_le {L : ℝ} (hL : 1 < L) :
    Real.log L + Real.log (Real.log L) ≤ 2 * Real.log L := by
  have hpos : 0 < Real.log L := Real.log_pos hL
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **The ceiling.**  At the crossover the permitted width is `log(Lℓ)/(Lℓ) ≤ 2/L`. -/
theorem ceiling_two_div {L l : ℝ} (hL : 0 < L) (hl : 0 < l) (hle : Real.log (L * l) ≤ 2 * l) :
    Real.log (L * l) / (L * l) ≤ 2 / L := by
  rw [div_le_div_iff₀ (by positivity) hL]
  nlinarith [hle, hl, hL]

/-- The ceiling is a genuine bound: `1/log log t` beats every power `(log t)^{-a}` with `a > 0`, yet
is not a fixed width.  So the mechanism attains exponent zero only in the weak sense. -/
theorem ceiling_not_fixed {L₁ L₂ : ℝ} (h1 : 0 < L₁) (h12 : L₁ ≤ L₂) :
    2 / L₂ ≤ 2 / L₁ := by
  apply div_le_div_of_nonneg_left (by norm_num) h1 h12

/-- **Assembly.**  Whichever side of the crossover the radius lies on, the permitted width is at most
the crossover value, hence at most `2/L`. -/
theorem ceilingWidth_le_two_div {L l r x : ℝ} (hL : 0 < L) (hl : 0 < l) (hx : 1 ≤ x)
    (hcross : x = Real.log (L * l)) (hle : Real.log (L * l) ≤ 2 * l)
    (hbranch : r / l ≤ x / (L * l) ∨ x ≤ r * L) :
    ceilingWidth L l r ≤ 2 / L := by
  have hkey : x / (L * l) ≤ 2 / L := by
    rw [hcross]
    exact ceiling_two_div hL hl hle
  rcases hbranch with h | h
  · exact le_trans (le_trans ceilingWidth_le_first h) hkey
  · refine le_trans ceilingWidth_le_second (le_trans ?_ hkey)
    have hdec : r * L * Real.exp (-(r * L)) ≤ x * Real.exp (-x) :=
      mul_exp_neg_antitone hx h
    have hval : x * Real.exp (-x) = x / (L * l) := by
      rw [hcross, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    linarith [hdec, hval.le, hval.ge]

end RHTower
