# Infinite prime--infinity root-conormal transgression

- **ID:** `infinite-prime-infinity-root-conormal-transgression`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / SOURCE-COMPARISON AND SEMI-INFINITE PHASE TARGET
- **Status:** `[RAW A_INFINITY AND ONE PORT CONSTRUCTED IN DERIVED MODEL]`
  `[LITERAL ROUTE-L COMPARISON OPEN] [NO RH CLAIM] [NO LEAN WRITTEN]`
- **Parent theorems:**
  `../../2-fully-proven/constraint-relativity/prime-infinity-port-capacity-and-root-conormal-law.md`,
  `../../2-fully-proven/constraint-relativity/prime-radial-excess-intersection-discriminant-law.md`.

## Frontier correction

Raw root conormal and one port no longer require conjectural rank collapse. For
`f_p(a)=p^(Ma)-1`, prime-radial Koszul object has

\[
 H_0(K_F)=\mathbb C,
 \qquad
 H_1(K_F)\cong
 \mathcal A_F
 =\{(v_p)_{p\in F}:\sum_{p\in F}v_p=0\},
 \qquad
 H_j(K_F)=\bigwedge^j\mathcal A_F,
 \tag{1}
\]

and exact observer Smith staircase

\[
 \operatorname{coker}J_F
 \cong\bigoplus_{j=1}^{|F|-1}\mathbb C[[a]]/(a^j).
 \tag{2}
\]

Thus one port is `H_0`, root conormal is `H_1`, and higher syzygies coexist in one excess derived
intersection without identifying distinct prime units. Normalized discriminant divisor is
`[a=0]` for every cutoff. Previous “singular cohomology must collapse A_infinity to one line” was
wrong architecture.

## Open conjecture: source-normal semi-infinite comparison

Construct coefficient-faithful comparison from prime-radial derived intersection to literal
rational-Witt/Milnor/Gamma source history, together with source-normal semi-infinite determinant
phase

\[
 K_\infty^{\mathrm{rad}}
 \xrightarrow{\operatorname{Comp}_{\mathrm{src}}}
 C_{\mathrm{rel}}^{\mathrm{Witt}/\Gamma}
 \xrightarrow{\mathfrak S_\mu}
 \mathscr S'(\mathbb R)
 \tag{3}
\]

such that:

1. construction occurs before Xi divisor choice;
2. finite prime valuation cocycles and Smith jet staircase are retained coefficientwise;
3. `H_0` maps to existing unique Stokes orientation and `H_1` to resolved prime conormal;
4. no relation identifies distinct prime units and no scalar contraction precedes comparison;
5. compatible cutoff determinant phases use source-derived semi-infinite/Tate polarization;
6. comparison identifies Route-L obstruction with completion curvature
   `Omega_(mu,Gamma)=S_mu G_Gamma D`;
7. literal source boundary identity, not defined cone, proves flatness on canonical class.

## Why semi-infinite phase is now hard core

Finite top determinant line is `wedge^(|F|-1) A_F`. Its degree increases at every cutoff; no top
degree exists in exterior algebra `wedge^* A_infinity`. Therefore finite determinant phases do not
stabilize as ordinary line. Any infinite phase needs extra restricted-Grassmannian/Tate or
determinant-gerbe polarization, and source must choose it before Xi divisor. Arbitrary zeta
regularization is rejected.

## First exact subproblem

For primes `{2,3}`, compare canonical generator of

\[
 H_1(K_{2,3})
 =\{(c_2,c_3):c_2\log2+c_3\log3=0\}
\]

with ordered prime difference boundary already present in Green/Bockstein source. Prove evaluation
intertwines Smith classes `R/(a),R/(a^2),...` with actual leading Xi jets before completion. At
three primes, retain two-dimensional `H_1` and length-three observer defect rather than collapsing
them to scalar.

## Fatal tests

Reject candidate if it:

1. ignores proved prime-radial Koszul model and reinvents raw conormal by false common inverse;
2. identifies `U_p=U_q`;
3. preserves every valuation derivation strictly;
4. contracts by logarithmic Kummer covector before coefficient-faithful comparison;
5. chooses zero-dependent weights;
6. defines semi-infinite determinant or singular cohomology to have desired rank one;
7. assumes source-normality/positivity equivalent to RH;
8. lacks transition maps across prime cutoffs or loses Smith jet staircase.

## Lean-return note

No Lean until literal finite-cutoff chain and transition proof are dependency closed. Existing
valuation/Kummer source files should be inspected only.

## Log

- 2026-08-08 — opened after port-capacity theorem classified two-prime false friend.
- 2026-08-08 — raw-collapse conjecture replaced by proved excess intersection; remaining problem
  is literal Route-L comparison and source-normal semi-infinite determinant phase.
