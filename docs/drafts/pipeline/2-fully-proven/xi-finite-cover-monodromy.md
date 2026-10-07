# Finite-cover monodromy of one exponentially tilted Xi source

- **ID:** RH-XIFCM-20261007
- **Stage:** 2-fully-proven; finite-cover paper proof closed, general Lean reduction outstanding
- **Parent:** `../1-in-progress/xi-marked-joint-monodromy.md`
- **Predecessor:** `../3-formalized/xi-polynomial-left-factors.md` (all final audits complete)
- **Verdict:** BRIDGE candidate; classical covering/parametrization reduction, no novelty claim

## Competing conjectures

Put d_a(s)=xi(s) exp(-a*s), a real, and U_a=C minus d_a^{-1}({0,-1}).
For every connected finite unramified cover Y -> C minus {0,-1}, its
pullback to U_a is connected. Equivalently, the image of pi_1(U_a) is dense
in the profinite completion of the free group on the two punctures.
This is a single-coordinate claim. It does not assert equality with the
discrete free group or independence between several arithmetic marks.

Competing possibility: a finite quotient beyond the cubic and cyclic
quotients retains an obstruction despite polynomial left-factor rigidity.
Such an obstruction would identify a compactified covering surface admitting
a nonconstant entire Xi lift that the polynomial analysis misses.

## Initial paper mechanism (completed below)

1. A proper subgroup in a finite monodromy quotient produces a nontrivial
   connected intermediate finite cover to which d_a on U_a lifts.
2. Compactify that cover over P1. Properness and the local branched-cover
   models extend the lift across each deleted source point. The resulting
   entire map C -> X avoids every point above infinity.
3. Uniformization/Picard says a compact curve with a nonconstant entire map
   avoiding a nonempty finite set must be P1 with at most two omitted points.
   The initial open dependency audit is closed on paper below. Its general
   Lean realization remains open.
4. With one point above infinity, the covering map is a polynomial and
   the lift is entire. The predecessor degree-one theorem excludes degree>1.
5. With two points above infinity, normalize them to 0 and infinity. The
   covering map is a Laurent polynomial with both positive and negative
   powers; the lift h:C->C* is entire and nowhere zero. Such a Laurent
   polynomial has a nonzero root b. On the zero-free right half-plane h
   omits 0,b, and 1/h omits 0,1/b. Schottky bounds both by exp(C*x), hence
   also bounds the Laurent polynomial, contradicting actual Xi ray growth.

The Laurent step needs no finite-order/Hadamard classification: zero-free
right-half-plane geometry and the already formalized Schottky estimate suffice.
If this proof closes, the next audit is the exact extent to which it is a
classical consequence of polynomial primeness or a known entire-function
covering theorem. Do not label it new science merely because Lean lacks it.

## Evidence / work log

- Corpus deep query launched directly with the documented research command:
  `finite branched cover entire lift compact Riemann surface polynomial Laurent omitted poles`.
  Output `/tmp/rh-xi-finite-cover-search-20261007.json`; completed partial=false,
  complete inventory 68195. All twenty candidate statements and twenty source
  arguments inspected; the suggested ingredient set supplied no applicable
  compact-curve parametrization theorem. Compiler coverage remains mostly
  pending/stale. A lexical OR follow-up and exact Lean text search found
  little Picard and specific uniformization data, not the general reduction.
- The Laurent increment is formalized and fully audited on
  `../3-formalized/xi-laurent-left-factors.md`. No full finite-cover theorem
  is yet formalized.

## Primary ancestry audit

[Pakovich, Theorems 2.1--2.4](https://pakovich.github.io/e.pdf) separates
normalization, Picard's genus restriction, and the stronger rational
parametrization result for entire algebraic curves. Its reduction then gives
a polynomial or Laurent-polynomial common outer function. This supports the
classical parent mechanism, not an automatic proof of the Xi finite-cover
statement. The theorem's parametrization definition includes cofinite image;
do not silently replace it by an arbitrary nonconstant map without proof.
Ancestry: Beardon--Ng (2006), Fuchs--Song (1985), Ng (2001), Picard (1887).
Pakovich's primary paper and arXiv record 0804.0739 were opened; §2 and its
references were read. Exact Xi/profinite novelty remains uncertified.

## Dependency-closed Laurent obstruction (selected next formal increment)

For every real a, polynomials P,Q over C, and entire nowhere-zero h, it is
impossible that P(h(s))+Q(1/h(s))=d_a(s) for every s. No restriction on the
degrees or on the two constant terms is needed. Every Laurent polynomial
has such a presentation, so this excludes all Laurent outer functions on
entire C*-valued lifts.

Proof: choose an actual Xi zero rho using the corpus's unconditional provider
and put b=h(rho), which is nonzero. The relation at rho says P(b)+Q(1/b)=0.
For Re(s)>1 the source is nonzero, so h(s)!=b. Thus h omits 0,b there, while
1/h omits 0,1/b. Both are holomorphic. The formalized Schottky half-plane
theorem bounds each along 1+t, t>=1, by exp(C*t). The polynomial transport
theorem bounds P(h) and Q(1/h) in the same way. Their sum is bounded by
exp((C1+C2+1)*t), since C1,C2>0 and 2<=exp(t) for t>=1. This contradicts
`RHTower.xi_tilt_not_exp_ray_bound a 1`.

Hostile verdict for this increment: BRIDGE, a short consequence of the
predecessor Schottky theorem. Its purpose is to remove the second possible
punctured-sphere lift, not to manufacture a new-science claim. The general
finite-cover extension and compact-curve reduction remain separate work.

## Completed finite-cover paper proof

Let F be any finite subset of C containing 0,-1, let V=C minus F, and
let U=d_a^{-1}(V). The function d_a is entire, nonconstant, and takes each
value only on a discrete set; U is a connected, locally path-connected open
subset of C. Fix a basepoint. Suppose its monodromy image in a finite
quotient G of pi_1(V) is a proper subgroup H. The connected cover V_H -> V
corresponding to the inverse image of H has degree [G:H]>1, and the covering
lifting criterion supplies a lift ell:U->V_H of d_a. This lift is holomorphic:
locally it is a holomorphic inverse sheet followed by d_a.

A finite cover of a punctured disk is a disjoint union of covers isomorphic
to z |-> z^e. Fill one point in each end of V_H over every point of
F union {infinity}. The resulting connected compact Riemann surface X
carries a holomorphic map pi:X->P1 extending the cover, of the same degree.
Compactness follows by taking the finite cover of the compact complement
of small puncture disks and attaching finitely many closed disks.

For r in C minus U, choose a small source disk containing no other such
point. The finite fiber pi^{-1}(d_a(r)) has disjoint coordinate neighborhoods.
After shrinking the source disk, properness confines ell on its punctured
disk to their union; connectedness confines it to one neighborhood. Its
coordinate is bounded there, so the removable-singularity theorem extends
ell holomorphically across r. These unique local extensions give ell:C->X
with pi ell=d_a everywhere. In particular ell is nonconstant and avoids
the nonempty finite set E=pi^{-1}(infinity).

Apply compact-surface uniformization. If X has genus at least two, lift ell
to its disk universal cover (C is simply connected); Liouville makes that
lift constant, a contradiction. If X has genus one, lift to C. A point of
E has infinitely many preimages under the lattice covering; the lifted
entire function omits all of them, contradicting little Picard. Hence X=P1.
This argument requires no cofinite-image assumption on ell. It is the
argument in §§4--5 of
[Beardon--Ng (2006)](https://www.acadsci.fi/mathematica/Vol31/beardon.pdf),
whose theorem statements and proofs were inspected directly.

Send one point of E to infinity by a Möbius coordinate. Then ell becomes
an entire function. Little Picard gives |E|<=2. If |E|=1, pi is a polynomial
and polynomial left-factor rigidity forces its degree to be one. If |E|=2,
send the other point to zero; ell becomes an entire nowhere-zero function
and pi is a Laurent polynomial. The preceding Laurent obstruction excludes
this case. Both contradict [G:H]>1. Thus every finite quotient receives the
full image. The equivalent connectedness of all finite pullback covers
follows from the transitive-action classification of connected covers.

No numerical computation, RH premise, zero-simplicity premise, or arbitrary
source replacement occurs. Classical dependencies are finite covering-space
classification and lifting, puncture completion, compact-surface
uniformization, removable singularities, little Picard, and rational
functions on P1. Actual Xi dependencies are the audited predecessor and
the Laurent argument. General Lean formalization remains outstanding.

## Stronger consequence exposed by this proof: new audit target

The proof did not use the particular finite puncture set. Candidate stronger
statement: C(d_a) is relatively algebraically closed in the field of global
meromorphic functions on C. For a meromorphic g algebraic over C(d_a),
normalize the compact algebraic curve of (d_a,g); the same entire lift avoids
all points over infinity. The polynomial/Laurent dichotomy would then force
degree one over the d_a coordinate. In characteristic zero this would also
give preservation of irreducibility for every polynomial over C(T) under
T |-> d_a. This formulation needs its own corpus, ancestry, and algebraic
normalization audit before being claimed proved or written in Lean.

Corpus audit for the stronger formulation: deep query completed partial=true,
inventory 68199; local model returned malformed JSON at filter_and_judge.
All twenty candidate and twenty source statements were inspected. They did
not settle the Xi statement. They did locate the existing global meromorphic
plane field, and exact follow-up inspection found `MeromorphicRationalRelativeClosure`
and `RegularExtensionMinpoly`: the algebraic preservation mechanism already
exists for the coordinate field C(z), not automatically for C(d_a).
Evidence: `/tmp/rh-xi-algebraic-closure-search-20261007.json`.

The finite-cover proof supplies the same relative-closure conclusion on paper:
a minimal polynomial of a nonrational meromorphic g over C(d_a), with its
finitely many coefficient poles and discriminant zeros removed, defines a
connected finite algebraic cover of the target. The actual g gives a lift,
contradicting the proved finite-cover statement. Irreducibility preservation
then follows directly: monic factor coefficients after base change are
algebraic over C(d_a), hence lie back in C(d_a). Lean must still construct
the analytic algebraic cover and justify this bridge; do not assume it.

Polynomial pole removal is formalized: `../3-formalized/xi-meromorphic-polynomial-lifts.md`.
Next increment: `../1-in-progress/xi-rational-left-factors.md`.
Remove the entire-right-factor restriction by proving pole removal for every
nonconstant polynomial, then applying the already audited degree-one theorem.
This is necessary groundwork for rational/compact-curve lift reduction;
it is not a substitute for the higher-degree irreducibility claim.
