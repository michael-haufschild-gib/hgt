# Local Frobenius homotopy-defect cocycle

- **ID:** `deninger-local-frobenius-homotopy-defect`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_LOCAL_FROBENIUS_HOMOTOPY_DEFECT`
- **Parent:** `deninger-frobenius-coherence-defect-spectrum`
- **Statement:** locally scalar Frobenius chain maps carry a canonical
  closed factorization defect satisfying a multiplicative cocycle law.

## Gates

- [x] Dependency-closed paper proof
- [x] Lean source written:
  `RHTower/Deninger/DeningerArithmeticFrobeniusHomotopyDefect.lean`
- [x] Direct `lake env lean` check
- [x] Final module build; equation `(6)` (commutation defect) also formalized

## Setup

Let \((C^\bullet,d)\) be a cochain complex over a commutative ring and let
\(F_n:C^\bullet\to C^\bullet\) be multiplicative cochain maps:
\[
 F_{mn}=F_mF_n.                                                       \tag{1}
\]
Let \(a_n\) be central scalars with \(a_{mn}=a_ma_n\).  Assume that on
each chart one has a degree \(-1\) homotopy \(h_n\) from \(F_n\) to
\(a_n\):
\[
 \delta h_n:=dh_n+h_nd=F_n-a_n\operatorname{id}.                     \tag{2}
\]

## Theorem

`[PROVED HERE] [DAC_LOCAL_FROBENIUS_HOMOTOPY_DEFECT]`

Define
\[
 c_{m,n}
 :=
 h_{mn}-F_mh_n-a_nh_m.                                               \tag{3}
\]
Then:

1. \(c_{m,n}\) is closed in the endomorphism complex:
   \[
   \delta c_{m,n}=0;                                                  \tag{4}
   \]
2. the defects satisfy the multiplicative two-cocycle law
   \[
   c_{lm,n}+a_n c_{l,m}
   =
   c_{l,mn}+F_lc_{m,n}.                                               \tag{5}
   \]

If \(mn=nm\), the two factor orders also give the closed commutation
defect
\[
 b_{m,n}
 =
 F_mh_n+a_nh_m-F_nh_m-a_mh_n.                                       \tag{6}
\]

## Proof

Because \(F_m\) commutes with \(d\) and \(a_n\) is central,
\[
\begin{aligned}
\delta(F_mh_n+a_nh_m)
 &=F_m\delta h_n+a_n\delta h_m\\
 &=F_m(F_n-a_n)+a_n(F_m-a_m)\\
 &=F_mF_n-a_ma_n\\
 &=F_{mn}-a_{mn}\\
 &=\delta h_{mn}.
\end{aligned}
\]
Subtracting gives `(4)`.

For `(5)`, expand both sides.  The left side is
\[
h_{lmn}-F_{lm}h_n-a_nF_lh_m-a_na_mh_l,
\]
and the right side is
\[
h_{lmn}-F_lF_mh_n-a_nF_lh_m-a_{mn}h_l.
\]
They agree by multiplicativity.  Equation `(6)` is the difference of two
homotopies with the same boundary, hence is closed.

## Interpretation

Local scalar purity does not imply globally scalar arithmetic cohomology
unless the \(h_n\) can be chosen with all classes \([c_{m,n}]\) and
\([b_{m,n}]\) coherently zero.  These classes are the exact obstruction
objects that a nonproper invariant-sheaf realization can retain.

This theorem does not prove that the defects are nonzero or that their
spectrum is the zeta divisor.

**Verdict:** `FULLY PROVEN ON PAPER; UNCONDITIONALLY FORMALIZED IN LEAN`.

## Log

- 2026-07-26 — Derived from multiplicativity of Frobenius and local
  scalar null-homotopies.  No zeta data or positivity premise occurs.

## Unconditional Lean formalization

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticFrobeniusHomotopyDefect.lean`

- `deningerHomotopyBoundary d h = d h + h d` — the endomorphism-complex boundary of `(2)`.
- `deningerFrobeniusHomotopyDefect F a h m n = h_{mn} - F_m h_n - a_n h_m` — equation `(3)`.
- `deningerCompositeHomotopy_boundary` — `δ(F_m h_n + a_n h_m) = F_{mn} - a_{mn}`, the
  computation at the heart of the Proof section.
- `deningerFrobeniusHomotopyDefect_boundary` — equation `(4)`, `δc_{m,n} = 0`.
- `deningerFrobeniusHomotopyDefect_cocycle` — equation `(5)`, the multiplicative two-cocycle law.
- `deningerFrobeniusCommutationDefect` and `deningerFrobeniusCommutationDefect_boundary` —
  equation `(6)`: for a commuting pair the two factor orders differ by a closed defect
  `b_{m,n} = F_m h_n + a_n h_m - F_n h_m - a_m h_n`, obtained as the difference of two
  homotopies with the same boundary.

Centrality of the scalars and commutation of `F` with `d` appear as explicit hypotheses, so no
ambient commutativity is assumed.  Axiom audit: `propext` only.
