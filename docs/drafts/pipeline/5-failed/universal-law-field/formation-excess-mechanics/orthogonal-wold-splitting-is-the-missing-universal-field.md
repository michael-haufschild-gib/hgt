# Orthogonal Wold splitting is the missing universal field

- **ID:** ULF-FEM-FAIL-1
- **Stage:** 5-failed
- **Conjecture:** The recurring decomposition into recovered and unrecovered sectors is itself the missing universal mathematical field.
- **Verdict:** [FAILED AS FIELD CORE] [REDISCOVERED MACHINERY] [POSITIVE SURVIVOR EXTRACTED] [NOT RH]

## 1. Proposed mechanism

Given an injection of source states (j:A\hookrightarrow B), linearize it as an isometry

\[
 T:\ell^2(A)\longrightarrow \ell^2(B).
\]

Then

\[
 \ell^2(B)=T\ell^2(A)\oplus\ker T^*,
 \qquad 1-TT^*=P_{B\setminus j(A)}.
\]

The tempting claim was that this orthogonal recovered/excess decomposition is the new field sought by
the corpus.

## 2. Fatal collision

This is standard isometry-defect and Wold machinery.  In greater generality it belongs to:

- Wold decompositions of isometries and product systems;
- exact and recollement decompositions induced by a split monomorphism;
- Fock models and unitary extensions of semigroup representations;
- endomotive decompositions of arithmetic endomorphisms into image and complement.

Current parents include Solel--Suryawanshi, *Wold decompositions for representations of product
systems* (arXiv:2601.09391), Skalski--Zacharias (arXiv:math/0702649), Li's odometer-semigroup Wold
theory (arXiv:2103.02070), and Yalkinoglu's endomotive/base-change constructions
(arXiv:1105.5022).  Replacing the words “isometry defect” by “formation excess” adds no theorem.

The same objection kills a bare direct-sum or cofiber field: exact categories, recollement, and
Karoubi completion already provide those containers.

## 3. Why the failure is useful

The corpus supplies more structure than a generic isometry:

1. the injection is the literal source power map (k\mapsto k^r);
2. the target contains a canonical positive arithmetic excess;
3. Mellin weights give the inherited and excess sectors canonical probabilities;
4. those probabilities compose under iterated source powers;
5. their negative logarithm has a coercive normalization-wall limit.

Generic Wold theory does not determine these weights, their crossed composition law, or their
boundary asymptotics.

## 4. Positive survivor

The strongest survivor is therefore not the splitting but the **source-weighted formation law**:

\[
 \text{source injection}
 \Longrightarrow
 \text{positive sector weight}
 \Longrightarrow
 \text{GNS defect probability}
 \Longrightarrow
 \text{spectral and information valuations}
 \Longrightarrow
 \text{additive surprisal work}.
\]

For ramification shells the work is

\[
 W_{m,r}(\sigma)
 =-\log\frac{S_m(r\sigma)}{S_{rm}(\sigma)},
\]

and it satisfies the exact crossed cocycle

\[
 W_{m,sr}(\sigma)
 =W_{rm,s}(\sigma)+W_{m,r}(s\sigma).
\]

It diverges as \(\sigma\downarrow1\).  This is a genuine positive/proper formation invariant, although
it still does not select the RH critical line.

The dependency-closed theorem is recorded in

`docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-excess-mechanics/ramification-gibbs-gns-defect-spectral-information-and-boundary-work-law.md`.

## 5. No-go closure status

- Generic orthogonal splitting: **retired**.
- Generic claim of new Wold/recollement geometry: **retired**.
- Source-weighted positive defect and surprisal cocycle: **survives**.
- RH selection from this invariant alone: **not proved**.
- Lean status: paper survivor only in this research pass; no Lean file written or built.

