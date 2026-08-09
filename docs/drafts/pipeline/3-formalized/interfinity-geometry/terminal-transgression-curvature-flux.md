# Terminal transgression and curvature flux

- **ID:** `terminal-transgression-curvature-flux`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `../../1-in-progress/interfinity-geometry/interfinity-geometry-program.md` · Theorems
  XVII--XXIII
- **Statement:** After a source-time cochain acquires its unique stable radial primitive, its
  remaining source defect is an exact commutator residue; cofinal normalizers kill flat residue,
  while curved cochains export the oriented difference of two bulk curvature faces.

## Goal

Extend endpoint geometry beyond coherent/Fock representations and identify exactly what survives
when future time becomes solvable but other source operations do not.

## Gates

- [x] 0 → 1 in-progress: source monoid, time ray, and curvature convention fixed
- [x] 1 → 2 fully-proven: flat, rigid, curved, and nonvacuity results proved below
- [x] 2 → 3 formalized: `terminal-transgression-curvature-flux-formalized.md`
- [ ] 3 → 4 publication-ready: package priority review remains open

## Setup

Let `M` be a topological monoid represented by continuous linear maps `pi(g)` on a Hausdorff
topological vector space `E`, preserving a continuously embedded subspace `H`.  Let
`r:R_+->M` satisfy `r(V+W)=r(V)r(W)` and assume

\[
 \pi(r(V))h\longrightarrow0\qquad(h\in H).
\tag{1}
\]

## Theorem A: flat terminal transgression

Let `b:M->H` be a normalized one-cocycle,

\[
 b(gh)=b(g)+\pi(g)b(h),
\tag{2}
\]

and suppose `b(r(V))->ell` in `E`.  Put `eta=-ell` and

\[
 \mathfrak R_b(g)=b(g)-(\pi(g)\eta-\eta).
\tag{3}
\]

Then:

1. `eta` is the unique radial stable primitive:

   \[
   b(r(V))=\pi(r(V))\eta-\eta,
   \qquad \pi(r(V))\eta\to0.
   \tag{4}
   \]

2. `R_b` is an `E`-valued one-cocycle and vanishes on the time ray.
3. For every `g in M` and every `phi(V)->infinity`,

   \[
   \mathfrak R_b(g)
   =-\lim_{V\to\infty}
      \left(b(r(V)g)-b(gr(\phi(V)))\right).
   \tag{5}
   \]

4. The radial primitive trivializes `b` on all of `M` exactly when every residue vanishes.  In
   particular, if `r(V)g=gr(phi(V))` eventually, then `R_b(g)=0`.
5. Left and right future orderings obey

   \[
   \mathfrak R_b(gr(V))=\mathfrak R_b(g),
   \qquad
   \mathfrak R_b(r(V)g)=\pi(r(V))\mathfrak R_b(g).
   \tag{6}
   \]

### Proof

The radial cocycle identity and the limit give, for fixed `W`,

\[
 \ell=b(r(W))+\pi(r(W))\ell.
\]

This is `(4)` with `eta=-ell`; also
`pi(r(V))eta=b(r(V))+eta->0`.  Two stable primitives differ by a fixed stable vector, hence are
equal.  Subtracting a coboundary from `(2)` proves item 2.

Expanding the difference in `(5)` gives

\[
 b(r(V)) +\pi(r(V))b(g)-b(g)-\pi(g)b(r(\phi(V))).
\]

The second term tends to zero by `(1)` and both radial terms tend to `ell`; the limit is
`ell-b(g)-pi(g)ell=-R_b(g)`.  This proves items 3 and 4.  Apply the cocycle law for `R_b` and use
`R_b(r(V))=0` to obtain `(6)`. `QED`

## Theorem B: curved terminal flux

Let `b:M->H` now be an arbitrary normalized one-cochain and define

\[
 \omega_b(g,h)=b(gh)-b(g)-\pi(g)b(h).
\tag{7}
\]

Assume `omega_b(r(V),r(W))=0` and `b(r(V))->ell`.  Define `eta` and `R_b` by `(3)`.  Then

\[
 \omega_b(g,h)+\omega_b(gh,k)
 =\pi(g)\omega_b(h,k)+\omega_b(g,hk),
\tag{8}
\]

`eta` satisfies `(4)`, `R_b` vanishes radially, and `omega_(R_b)=omega_b`.  If the curvature
difference below has a limit, then for every `phi(V)->infinity`,

\[
 \begin{aligned}
 \mathfrak R_b(g)
 &=-\lim_V\left(b(r(V)g)-b(gr(\phi(V)))\right)\\
 &\quad+\lim_V\left(
   \omega_b(r(V),g)-\omega_b(g,r(\phi(V)))
   \right).
 \end{aligned}
\tag{9}
\]

If `r(V)g=gr(phi(V))` eventually, the first limit is zero and

\[
 \mathfrak R_b(g)
 =\lim_V\left(
   \omega_b(r(V),g)-\omega_b(g,r(\phi(V)))
   \right).
\tag{10}
\]

### Proof

Expand `b(ghk)` along `(gh)k` and `g(hk)` to obtain `(8)`.  Radial flatness makes the restriction
of `b` a cocycle, so Theorem A's limit argument proves `(4)`.  A coboundary has zero curvature,
hence subtracting `d eta` leaves `(7)` unchanged and kills the radial restriction.

Use `(7)` twice:

\[
 \begin{aligned}
 b(r(V)g)-b(gr(\phi(V)))
 &=b(r(V))+\pi(r(V))b(g)+\omega_b(r(V),g)\\
 &\quad-b(g)-\pi(g)b(r(\phi(V)))-\omega_b(g,r(\phi(V))).
 \end{aligned}
\]

The non-curvature terms tend to `-R_b(g)` exactly as in Theorem A.  Rearrangement proves `(9)`;
the cofinal-normalizer relation proves `(10)`. `QED`

## Curved nonvacuity model

Take `M=R_+ x C_2`, `H=E=C`, with central involution `g`,

\[
 \pi(r(t))=e^{-t},\qquad\pi(g)=-1,
 \qquad
 b(r(t))=e^{-t}-1,qquad b(r(t)g)=0.
\tag{11}
\]

The time restriction is flat with stable primitive `eta=1`, but

\[
 \mathfrak R_b(g)=2,
 \qquad
 \omega_b(r(t),g)=1-e^{-t},
 \qquad
 \omega_b(g,r(t))=e^{-t}-1.
\tag{12}
\]

Therefore `(10)` gives `R_b(g)=2`.  Centrality kills flat transgression, but not curved flux.

## Free-source universality no-go

Before source relations are imposed, residues have no predictive content.  Given arbitrary
`h_1,...,h_n` in a finite-dimensional Hilbert space, take
`M=R_+ * F_n^+`, represent time by `e^(-t)I` and every free generator `x_j` by `I`.  Define a
cocycle `R` by `R(r(t))=0`, `R(x_j)=h_j`, and put

\[
 b(g)=\pi(g)\eta-\eta+R(g).
\]

Then the radial primitive is `eta` and `R_b(x_j)=h_j`.  Thus all restrictions must come from
arithmetic source relations, positivity/duality, or common-clock descent—not from residue or phase
formalism alone.

## Lean handoff notes

Theorems A and B are monoid representation and limit algebra.  Formalization needs a strongly
stable time ray, cocycles/cochains, and elementary limit transport.  Model `(11)` is a useful first
test.  No existing Lean file is designated.

## Boundary

Cocycle subtraction, Bianchi identity, and commutator expansions are standard.  Candidate-new
content is their forward-terminal use: a radial endpoint fixes the gauge, cofinal source relations
decide flat residue, and oriented bulk curvature imbalance becomes its boundary value.

