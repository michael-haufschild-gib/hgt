# Seam Division Source Split Requires FE Cancellation

- **ID:** seam-division-source-split-cancellation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / analytic source-split guardrail
- **Source:** `seam-log-derivative-weld-identity.md`;
  `archimedean-prime-cross-term.md`; `carrier-herglotz-rh.md`
- **Statement:** After division by the seam coordinate, the completed
  log-derivative is holomorphic, but its archimedean and prime summands are not.
  Each summand has a nonzero simple pole at the seam, and the functional equation
  cancels those poles exactly.

## Setup

Let

`Xi(w)=xi(1/2+w)`,

with

`xi(s)=1/2 s(s-1) pi^(-s/2) Gamma(s/2) zeta(s)`.

Write `s=1/2+w` and split the completed logarithmic derivative as

`Xi'(w)/Xi(w)=A(w)+P(w)`,

where

`A(w)=1/s+1/(s-1)-(1/2)log pi+(1/2)psi(s/2)`

and

`P(w)=zeta'(s)/zeta(s)`.

By `seam-log-derivative-weld-identity.md`, the seam-log Markov candidate is

`G_src(-w^2)=Xi'(w)/(w Xi(w))`.

## Theorem

The completed quotient

`(A(w)+P(w))/w`

is holomorphic at `w=0`, but the two source pieces `A(w)/w` and `P(w)/w` each
have a nonzero simple pole there. Their residues are opposite:

`Res_{w=0} A(w)/w = (1/2)(psi(1/4)-log pi)`,

and

`Res_{w=0} P(w)/w = -(1/2)(psi(1/4)-log pi)`.

Moreover,

`(1/2)(psi(1/4)-log pi)=-(1/2)(gamma+pi/2+3log 2+log pi)<0`,

so neither residue vanishes.

## Proof

The displayed formula for `xi` gives the logarithmic derivative split above.

The functional equation makes `Xi` even. Since `Xi(0)!=0`, the logarithmic
derivative `Xi'/Xi` is odd and vanishes at `w=0`. Therefore

`(A(w)+P(w))/w = Xi'(w)/(w Xi(w))`

has a removable singularity at `w=0`.

The archimedean summand is regular at `w=0`, and its value is

```text
A(0) = 1/(1/2) + 1/(-1/2) - (1/2)log pi + (1/2)psi(1/4)
     = (1/2)(psi(1/4)-log pi).
```

The standard digamma value

`psi(1/4)=-gamma-pi/2-3log 2`

gives

`A(0)=-(1/2)(gamma+pi/2+3log 2+log pi)<0`.

Thus `A(w)/w` has a nonzero simple pole at `w=0` with residue `A(0)`.

Since `A(w)+P(w)=Xi'(w)/Xi(w)` vanishes at `w=0`, one has

`P(0)=-A(0)`.

Therefore `P(w)/w` also has a nonzero simple pole at `w=0`, with the opposite
residue. The sum has no pole because these two residues cancel exactly.

## Consequence For The RH Route

The divided seam-log object is a completed object. It is not a termwise
Markov/Pick object on the archimedean and prime pieces.

A proof cannot split

`G_src(-w^2)=A(w)/w+P(w)/w`

and then ask each summand to be separately positive, Herglotz, Pick, or
Stieltjes near the seam: neither summand is even holomorphic there. The
functional equation supplies local cancellation, not a square-test inequality.

Thus the source theorem must control the completed sum after the seam
division, or must keep the cancellation mechanism inside the source-built
boundary object. Piecewise positivity of the divided source terms is not a
valid feeder for the repair theorem.

## Source Boundary

This theorem is a local analytic guardrail. It proves no RH positivity and no
zero localization. Its role is to prevent a source split from being promoted to
a Markov/Stieltjes proof before the functional-equation cancellation has been
accounted for.

## Gates

- [x] 0 -> 1 in-progress: divided source-split pole issue isolated.
- [x] 1 -> 2 fully-proven: residue calculation and FE cancellation written.
- [x] 2 -> 3 formalized (2026-08-17): residues, functional-equation cancellation, and the digamma
  value `ψ(1/4)` all proved unconditionally — the digamma value is *derived*, not imported.  See the
  Lean formalization section below.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation after checking
  that the existing seam-log derivative identity normalized the completed
  object but did not record the nonzero residues of the divided source pieces.

## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/RHTower/SeamDivisionSourceSplit.lean`
(wired into the `GaloisForLFunctions.RHTower` umbrella).

| Card step | Lean name |
|---|---|
| `ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)` | `VorosClosedForm.xiFun`, `elemFactor` |
| the split `ξ'/ξ = A + P`, `A = 1/s + 1/(s−1) − ½logπ + ½ψ(s/2)`, `P = ζ'/ζ` | `SeamSplit.archSummand`, `primeSummand`, `logDeriv_xiFun_split` |
| the functional equation `ξ(1−s) = ξ(s)` | `SeamSplit.xiFun_one_sub` (from `completedRiemannZeta_one_sub`) |
| `Ξ(w) = ξ(½+w)` is even | `SeamSplit.Xi`, `Xi_even` |
| `Ξ'/Ξ` odd, hence vanishing at the seam | `SeamSplit.deriv_xiFun_half`, `logDeriv_xiFun_half` |
| `A(0) = ½(ψ(1/4) − logπ)` | `SeamSplit.archSummand_half` |
| **`ψ(1/4) = −γ − 3 log 2 − π/2`** | `SeamSplit.digamma_one_quarter` (via `digamma_half`, `digamma_three_quarters_sub_quarter`) |
| `A(0) = −½(γ + π/2 + 3log2 + logπ) < 0` | `SeamSplit.archSummand_half_real`, `archSummand_half_ne_zero` |
| `P(0) = −A(0)`, both nonzero | `SeamSplit.primeSummand_half`, `primeSummand_half_ne_zero` |
| `Res_{w=0} A(w)/w = A(0)` | `SeamSplit.residue_archSummand` |
| `Res_{w=0} P(w)/w = −A(0)` | `SeamSplit.residue_primeSummand` |
| the completed quotient has no pole: the residues cancel | `SeamSplit.residue_sum` |
| **the whole theorem** | `SeamSplit.seam_division_source_split` |

**The gate's "imported digamma value" is not imported.**  `ψ(1/4) = −γ − 3log2 − π/2` is *derived*
from the Gauss duplication formula and Euler's reflection formula, both already in the tree
(`HTGeometry.digamma_duplication`, `HTGeometry.digamma_reflection`), together with mathlib's
`Complex.digamma_one : ψ(1) = −γ`: duplication at `s = ½` gives `ψ(½) = −γ − 2log2`, duplication at
`s = ¼` gives `ψ(¼) + ψ(¾) = 2ψ(½) − 2log2`, and reflection at `s = ¼` gives `ψ(¾) − ψ(¼) = π·cot(π/4) = π`.

**The one input the card leaves implicit.**  The split at the seam needs `ζ(1/2) ≠ 0`, because the
card's `P(0) = ζ'/ζ(1/2)` and its step "`Ξ(0) ≠ 0`, so `Ξ'/Ξ` is odd" both require it.  This is
supplied unconditionally by the corpus's `RHTower.riemannZeta_real_strip_ne_zero`: `ζ` is nonzero on
the real segment of the critical strip.  (`logDeriv_xiFun_half = 0` itself is proved *without* that
input, since `logDeriv f x = deriv f x / f x` and the evenness of `Ξ` already forces `deriv Ξ 0 = 0`.)

**Residue formulation.**  "Nonzero simple pole with residue `r`" is formalized as
`Tendsto (fun w => w · (f(½+w)/w)) (𝓝[≠] 0) (𝓝 r)` together with `r ≠ 0`; the cancellation is the
same limit for the sum with `r = 0`.  Negativity of `A(0)` uses mathlib's
`Real.one_half_lt_eulerMascheroniConstant` for `γ > 0`.

**Not formalized, and not an obligation of this card:** the "Consequence For The RH Route" section,
which is a methodological scope statement about which proof strategies are excluded, not a
mathematical proposition.  Its mathematical content is `seam_division_source_split`.

Verification: `lake build GaloisForLFunctions.RHTower.SeamDivisionSourceSplit` — PASS; `#print axioms`
on all fifteen named results reports only `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-17 — Formalized unconditionally in Lean 4 and promoted to stage 3.  The `ξ` functional
  equation, the evenness of `Ξ`, the vanishing of the completed seam logarithmic derivative, the
  closed-form archimedean residue with its derived `ψ(1/4)` value, the exact opposite prime residue,
  and the cancellation of the two poles are unconditional Lean theorems.
