# Continuous prime measures admit arbitrarily small finite defects

- **ID:** continuous-prime-finite-defect-rigidity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A55.
- **Statement:** Finite uncompleted `L¹` or `L²` functional-equation defect does not force a positive Beurling prime-power measure to be the Riemann measure.

## Exact construction

Let `Q` be the pushforward under `x↦exp x` of `x exp(−x) dx` on
`x>0`. It is a positive atomless probability measure supported above `1`,
with Mellin transform `1/(s+1)²` for `Re s>−1`. For `ε>0`, put

`Pε=Pζ+εQ`, `Mε(s)=exp(ε/(s+1)²)`, `Fε(s)=ζ(s)Mε(s)`.

The convolution exponential of `Pε` has unit atom at `1` and Mellin
transform `Fε` on `Re s>1`. The prime measure differs from `Pζ`.
Set `βε=exp(ε/4)/2` and
`Eε(s)=Mε(s)Λζ(s)−βεΓℝ(s−1)`, with its removable value at `1`.
Then `Eε` satisfies the full Hamburger strip conditions. Its uncompleted
reflection defect is

`gε(t)=ζ(1/2+2it)[Mε(1/2+2it)−Mε(1/2−2it)]`.

## Proof

Multiplicative convolution turns Mellin transforms into products; summing
the convolution exponential gives `exp(Mellin(Pε))`. The density integral
is the elementary complex Laplace integral of `x`, yielding the stated
rational transform. At `s=1`, the pole residues of `MεΛζ` and
`βεΓℝ(s−1)` agree. A divided difference of `Mε` and the regularized Gamma
factor give a holomorphic remainder on `Re s>0`. Uniform vertical decay
of completed zeta and shifted Gamma, plus compactness, gives
`|Eε(s)|≤Cε/(1+Im(s)²)` throughout `1/2≤Re s≤3/2`.

On `Re s=1/2`, the exponent difference has exact modulus
`6ε|Im s|/(9/4+Im(s)²)²`. The exponential difference is at most
`exp(ε)` times this modulus. The unconditional critical-line bound
`|ζ(1/2+it)|≤K(1+|t|)` therefore gives
`|gε(t)|≤C ε exp(ε)/(1+t²)`, with `C` independent of `ε`.
This majorant belongs to both `L¹` and `L²`.

## Positive survivor

For every `δ>0`, some `0<ε≤1` gives a nontrivial positive continuous
Euler perturbation with `|gε(t)|≤δ/(1+t²)`. Its continuation on
`Re s>0` preserves every zero of zeta, since `Mε` never vanishes.
Thus zero preservation and arbitrarily small finite defect coexist with
nonclassical positive prime measures. No global meromorphy across `−1`
is asserted.

## Lean status

The Mellin identity, atomlessness and probability of `Q`, positive Euler
identity, nontriviality, zero preservation, `L¹`, `L²`, and small majorants
are verified in the first four new `EulerFETransportTheory` modules.
The full strip module and the capstone
`ContinuousPrimeMeasuresAreNotRigidUnderFiniteDefects.lean` still need
successful checks and final audits. The route remains open until then.
