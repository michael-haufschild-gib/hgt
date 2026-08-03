# Resolved-provenance off-axis quotient rigidity

- **ID:** `deninger-resolved-provenance-off-axis-quotient-rigidity`
- **Stage:** 2-fully-proven
- **Type:** SOURCE-QUOTIENT CLASSIFICATION / FRONTIER REDUCTION
- **Label:** `DAC_RESOLVED_PROVENANCE_OFF_AXIS_QUOTIENT_RIGIDITY`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** away from zero Cartan displacement, resolving Hellinger--Gamma
  cofaces by unchanged Calderón--Witt incidence provenance leaves exactly
  provenance in the closed relative quotient.  No Hodge-channel class
  survives alongside it.

## Set-up

Fix distinct source primes and write (H) for their completed
Calderón--Witt incidence carrier.  The ordinary completed Hellinger--Gamma
carrier is

\[
  K=H\oplus H.
\]

For modular displacement (a), let (C_a\subset K) be the closed linear
span of all adjacent balanced cofaces.  The already-proved closed-saturation
law is

\[
 C_a=
 \begin{cases}
   \Delta_H,&a=0,\\
   K,&a\ne0.
 \end{cases}                                                   \tag{1}
\]

Resolve provenance before differencing by putting

\[
 \widetilde K=K\oplus H,
 \qquad
 \widetilde v_n(x)=(v_n(x),x).
\]

Then every resolved adjacent coface is

\[
 \widetilde v_{n+1}(x)-\widetilde v_n(x)
   =(v_{n+1}(x)-v_n(x),0).                                    \tag{2}
\]

Let \(\widetilde C_a\subset\widetilde K\) be their closed linear span and
let (P:\widetilde K\to H) be provenance projection.

## Theorem

`[THEOREM] [DAC_RESOLVED_PROVENANCE_OFF_AXIS_QUOTIENT_RIGIDITY]`

For every (a\ne0),

\[
  \boxed{\widetilde C_a=K\oplus0=\ker P.}                     \tag{3}
\]

Consequently (P) induces a canonical linear equivalence

\[
 \overline P_a:\widetilde K/\widetilde C_a
      \xrightarrow{\;\sim\;} H,                              \tag{4}
\]

whose inverse is

\[
 x\longmapsto[(0,x)].                                         \tag{5}
\]

Thus every linear observation of the off-axis resolved relative quotient
factors uniquely through completed incidence provenance.  There is no
remaining off-axis Hodge marginal on which a separate annihilation argument
could act.

At (a=0), the same argument and `(1)` give the full phase boundary

\[
 \widetilde C_0=\Delta_H\oplus0.                              \tag{6}
\]

The zero-displacement quotient therefore retains one Hodge antidiagonal in
addition to provenance; this exceptional summand disappears at every
nonzero displacement.

## Proof

Equation `(2)` gives

\[
 \widetilde C_a\subseteq\ker P.                               \tag{7}
\]

Let \(\iota:K\to\widetilde K\) be \(u\mapsto(u,0)\).  It is a continuous
linear embedding, and `(2)` says that it sends every ordinary adjacent
coface generator to the corresponding resolved generator.  Hence it sends
the algebraic span of ordinary cofaces into the algebraic span of resolved
cofaces.  Continuity and closedness of \(\widetilde C_a\) extend this to

\[
 \iota(C_a)\subseteq\widetilde C_a.                            \tag{8}
\]

If (a\ne0), `(1)` makes the left side of `(8)` equal to
\(\iota(K)=K\oplus0=\ker P\).  Combine with `(7)` to prove `(3)`.
For (a=0), `(1)` gives `(6)` by the same two inclusions.

The descended map in `(4)` is onto because
\(P(0,x)=x\).  If its value on a quotient class represented by (z) is
zero, then (z\in\ker P=\widetilde C_a\) by `(3)`, so the class is zero.
Thus it is bijective, and `(5)` follows directly.  Unique factorization of
linear observations is transport across this equivalence.

## Hostile audit

- This theorem does **not** annihilate actual Green provenance.  It proves
  that off axis, provenance is the entire resolved quotient, so annihilation
  must hit that explicit class itself.
- It does not use RH, a zero-location premise, positivity, or a divisor-fed
  choice of quotient.
- It is stronger than the existing split injection.  A left inverse only
  says provenance survives; `(3)`--`(4)` say nothing else survives off axis.
- Appending another Hodge coface, completing the same two channels again, or
  choosing a different observer on their quotient cannot move Route L:
  closed saturation has already erased those channels.
- The theorem does not identify the missing arithmetic differential.  It
  changes its exact type: off axis it must be a packet-valued operation on
  completed incidence provenance, not a mixed Hodge/provenance observer.

## Novelty audit

Repository search found the ordinary phase law `(1)`, the inclusion
\(\widetilde C_a\subseteq\ker P\), and a split injection of provenance into
the quotient, but no reverse inclusion, quotient classification, or
off-axis universal factorization.  The result is specific to the completed
Hellinger--Gamma/Calderón--Witt source constructed here; the Deninger,
Meyer, and Paugam literature does not contain this resolved coface object.
Novelty is therefore internal and structural; external priority remains
provisional pending specialist review.

## Route-L consequence

The unresolved source identity is now forced to have form

\[
 A_{p,a}(x_G)=0
 \quad\text{on }H,
\]

where (x_G) is actual completed Calderón--Witt Green provenance and
\(A_{p,a}\) retains packet/off-diagonal incidence data.  There is no
off-axis Hodge quotient left to absorb or cancel (x_G).  This excludes a
whole class of false repairs while preserving exact nonzero source datum
that a genuine arithmetic annihilator must kill.

## Formalization target

`formal/GaloisForLFunctions/RHTower/`
`DeningerCompletedXiHellingerGammaResolvedProvenanceSaturation.lean`

Required capstones:

1. resolved closed coface span equals provenance kernel for `a ≠ 0`;
2. descended provenance projection is bijective;
3. canonical linear equivalence with completed incidence provenance;
4. source insertion is its inverse.

