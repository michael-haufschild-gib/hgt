# Heat persistence in shrinking zero neighborhoods

- **ID:** wd-shrinking-window-heat-persistence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); unconditional zero displacement and multiplicity counting
- **Source:** [WD](../1-in-progress/wd-directed-source-extinction.md); [fixed-depth persistence](wd-mean-field-heat-persistence.md)
- **Statement:** There are absolute `c>0`, `X₀≥4096` such that, for every `X≥X₀`, `0<d≤1/2`, `t>0`, and `t log X≤c d²`, every unheated zero `z` with `Re z=X`, `|Im z|≤1/2` has a heat zero in `|w-z|≤d`.
- **Counting:** With absolute constants and a depth-independent height threshold, every finite family `F` of Xi zero copies in `[X,2X]` at depth at least `d` satisfies `#F≤C log X·N(t)` whenever `0<t` and `t log X≤c d²`.

## Scope

The existing inverse-logarithmic theorem fixes the depth before choosing
its constants and height threshold. It supplies no uniform statement
when the depth shrinks with height or heat. This theorem gives actual zero
displacement at scale `sqrt(t log X)`, with a single constant and a single
height threshold. A zero of depth greater than that displacement forces
a nonreal heat zero in a shrinking neighborhood. No upper bound on
`N(t)` or source-cap extinction is claimed.

## Source inputs and mechanism

Actual heat factorization, uniform for `t log X≤1`:
`H_t(X-16i+w)=P(w)g(w)`, with degree `n≤C log X`, zero-free `g` on
radius 18, and `g'/g`, `(g'/g)'` bounded by `C log X` on fixed smaller
disks (`HeatLocalCofactor.lean`). The global relative envelope and
translated reverse Gaussian identity are already formalized.

The key estimate retains the normalized zero factors after cancelling
their linear logarithmic slopes. Their error is quadratic on the whole
plane, including segments crossing zeros. Combined with the smooth
cofactor, this controls the centered saddle profile on a fixed real
interval. A weaker floor `exp(-C log X/d)` then suffices for the complete
far tail. The proof below keeps all constants independent of `d`.

## Lean declarations

Paths are relative to `formal/GaloisForLFunctions/`.

| Module | Main declarations |
|---|---|
| `HTGeometry/CenteredFactorProduct.lean` | `GaloisForLFunctions.HTGeometry.norm_centered_root_product_sub_one_le`; `GaloisForLFunctions.HTGeometry.norm_centered_factorization_sub_one_le` |
| `RHTower/HeatShrinkingWindow.lean` | `RHTower.DeBruijn.exists_riemannHeat_shrinking_window_bounds` |
| `RHTower/HeatZeroDisplacement.lean` | `RHTower.DeBruijn.exists_riemannHeat_zero_in_shrinking_ball`; `RHTower.DeBruijn.exists_nonreal_riemannHeat_zero_at_uniform_depth_scale` |
| `RHTower/HeatUniformDepthZeroDensity.lean` | `RHTower.DeBruijn.exists_card_deep_le_heat_count_at_uniform_depth_scale` |

All four modules passed final plain Lean checks without warnings.
Every analytic input to the actual heat theorems is discharged; no
arithmetic estimate or unknown zero-distribution property is assumed.

## Complete paper proof

**[PROVED HERE; formalized in the declarations above.]** The source
inputs are actual-source theorems formalized in the linked card.

Write `L=log X`, `N=|xiLine X 16|>0`, and `b=X-16i`. Enlarge the
absolute height threshold so `L≥20`. Let `C₀>0` be the uniform local
cofactor constant and `G>0` the global relative-growth constant. Set

\[
C=40C_0,\quad R=1/32,\quad
M=8+2G+C+\log32,
\]
\[
c=\min\left(1,\frac1{64C},
 \frac{R}{8(C+G)},\frac{R^2}{8M}\right)>0.
\]

Take `0<d≤1/2`, `t>0`, `tL≤c d²`, and an unheated zero `z` with
`Re z=X`, `|Im z|≤1/2`. Then `t≤1/8` and `tL≤1`, so all actual heat
source bounds apply. Suppose no heat zero lies in the closed radius-`d`
disk about `z`.

### 1. Uniform disk estimates

Use `H_t(b+w)=P(w)g(w)` with `n=deg P≤C₀L`. Discard zero exponents;
every remaining factor is an actual heat zero. If `|s-z|≤d/8`, each
factor has distance at least `d/2` from `s`, and `|s-b|≤33/2+d/8`.
The exact logarithmic-derivative split gives

\[
|H_t'(s)/H_t(s)|\le2n/d+C_0L\le CL/d.
\]

The cofactor floor yields

\[
|H_t(s)|\ge\frac N8(d/36)^n e^{-C_0L}
 \ge\frac N8e^{-CL/d}.
\]

For the last inequality, `log(36/d)≥0` and
`1+log(36/d)≤36/d`. Hence
`n log(36/d)+C₀L≤36C₀L/d≤CL/d`.

For any complex `w`, put `E(w)=(1+w)exp(-w)`. The corpus gives
`|E(w)|≤exp(|w|²/2)` globally and `|E(w)-1|≤|w|²` on `|w|≤1`.
These imply

\[
|E(w)-1|\le e^{2|w|^2}-1
\]

globally: for `|w|>1`, put `v=|w|²`; then `exp(v)≥2` and
`exp(v/2)+1≤exp(2v)-1`. If two errors are bounded by `exp(A)-1`
and `exp(B)-1`, the product error is at most `exp(A+B)-1`, by
`ab-1=(a-1)b+(b-1)`.

Normalize `P` at `s-b` and cancel its linear slope. The resulting
product is exactly the product of `E(u/(s-b-a))^{m_a}`. Its error is
at most `exp(8C₀L u²/d²)-1` for every real `u`, including segments
crossing polynomial zeros. For `|u|≤R`, the cofactor's centered error
is at most `exp(C₀L u²)-1`. Indeed, the disk of radius `4R=1/8`
about `s-b` lies inside radius `67/4`, where `(g'/g)'` is bounded by
`C₀L`. The existing logarithmic-slope Grönwall theorem applies there.
Multiplying both centered factors gives

\[
\left|e^{-uH_t'(s)/H_t(s)}\frac{H_t(s+u)}{H_t(s)}-1\right|
 \le e^{(CL/d^2)u^2}-1 \qquad(|u|\le R).
\]

### 2. Saddle and complete Gaussian error

Since `2tCL/d≤d/32`, the holomorphic map
`s↦z+2tH_t'(s)/H_t(s)` maps the radius-`d/16` disk into the closed
radius-`d/32` disk. The proved holomorphic disk fixed-point theorem
supplies `s=z+2ta`, with `|s-z|≤d/32` and `a=H_t'(s)/H_t(s)`.
Put `F(u)=exp(-ua)H_t(s+u)/H_t(s)` and `K=CL/d²`.

The actual global relative envelope and the floor above give, for all
real `u`,

\[
|F(u)|\le e^{E L+D L|u|},\qquad
E=8+2G+C/d,\quad D=C/d+G.
\]

Here `|Im s|≤1` and `|Re s-X|≤1`, so the unit-strip envelope applies;
the factor 8 is absorbed using `8≤exp(8L)`. The constant choices imply

\[
tK\le1/64,\quad tDL\le R/8,\quad
tL(E+\log32)\le R^2/8,
\]

because `d²D≤C+G` and `d²(E+log32)≤M`. The complete Gaussian error
theorem, including integrability, therefore gives

\[
\left|\int_{\mathbb R}g_t(u)F(u)\,du-1\right|
 \le8tK+8e^{EL-R^2/(8t)}
 \le1/8+1/4<1/2.
\]

The exact translated reverse identity reads

\[
H_0(z)=e^{-ta^2}H_t(s)\int_{\mathbb R}g_t(u)F(u)\,du.
\]

All three factors on the right are nonzero, contradicting `H₀(z)=0`.
Thus a heat zero lies within distance `d` of `z`.

### 3. Nonreal persistence and multiplicity counting

Apply displacement with radius `d/2` to an unheated zero of depth at
least `d`. If `tL≤(c/4)d²`, its heat zero remains nonreal and within
distance `d/2`. All constants and the height threshold are independent
of `d`.

For a finite set `F` of Xi zero copies in `[X,2X]` at depth at least
`d`, transform each copy to its unheated spectral zero. Since
`log T≤2log X`, the preceding theorem applies to every copy when
`t log X≤(c/8)d²`. Choose one resulting nonreal heat zero per copy.
Every fibre lies in a unit ordinate window and thus contains at most
`2C_xi log X` copies, by the actual local Xi multiplicity theorem.
The finite image has cardinality at most `N(t)`, since each distinct
nonreal heat zero has multiplicity at least one. Hence

\[
\#F\le2C_\xi\log X\,N(t).
\]

The constants and height threshold are uniform over `0<d≤1/2`.
This is the earlier necessity statement with universal quadratic depth
dependence. It gives no independent upper bound on `N(t)` and no WD
extinction theorem.

## Validation and remaining work

Each command passed without warnings, run individually from `formal/`:

```sh
lake --old env lean GaloisForLFunctions/HTGeometry/CenteredFactorProduct.lean
lake --old env lean GaloisForLFunctions/RHTower/HeatShrinkingWindow.lean
lake --old env lean GaloisForLFunctions/RHTower/HeatZeroDisplacement.lean
lake --old env lean GaloisForLFunctions/RHTower/HeatUniformDepthZeroDensity.lean
```

Imports are wired into `HTGeometry.lean` and `RHTower.lean`; umbrellas
were not compiled. The API scratch file was removed. No web search,
novelty checks, numerical experiments, or axiom checks were performed.

The necessity transfer is closed uniformly in depth. The next required
input is an arithmetic upper count or signed-source upper bound strong
enough to force extinction. These theorems do not prove any upper-count
rung, near-axis extinction, or RH. The WD goal remains active.
