# Derived/homotopy endpoint insufficiency for torsion and filling cost law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [UNIVERSAL-LAW FIELD]
  [HOSTILE PLG BOUNDARY] [HOMOTOPY TYPE IS INSUFFICIENT]
  [SIMPLE/WEIGHTED ENRICHMENT FORCED] [NOT RH] [NO LEAN]

## 1. Derived-category no-go

Let \(k\) be a field and let

\[
 C(u):0\longrightarrow k\xrightarrow{u}k\longrightarrow0,
 \qquad u\in k^\times,
\tag{HI.1}
\]

carry its declared bases.

### Theorem 1.1

Every \(C(u)\) is isomorphic to zero in the bounded derived category \(D^b(k)\). Therefore every
invariant

\[
 F:\{\text{based finite complexes}\}\longrightarrow Y
\tag{HI.2}
\]

that factors through \(D^b(k)\) is constant on the family \(\{C(u)\}_{u\in k^\times}\).

But the determinant history

\[
 \tau(C(u))=u
\tag{HI.3}
\]

is not constant. Hence determinant torsion does not factor through the derived category.

### Proof

Multiplication by \(u\neq0\) is an isomorphism, so \(C(u)\) is acyclic and therefore zero in
\(D^b(k)\). Any functor factoring through the derived category takes isomorphic objects to the same
value. Equation (HI.3) varies with \(u\).

## 2. Endpoint and unweighted-topology no-go

In

\[
 G=\langle a,b\mid[a,b]\rangle\cong\mathbb Z^2,
\tag{HI.4}
\]

put \(w_n=a^nb^na^{-n}b^{-n}\).

### Theorem 2.1

Every invariant of words that factors only through the represented group element is constant on
\(\{w_n\}\), because every \(w_n\) represents the identity. It cannot recover

\[
 \operatorname{Area}(w_n)=n^2.
\tag{HI.5}
\]

Likewise, the standard minimum fillings are all topological disks. Any invariant factoring only
through the unweighted homeomorphism type of the filling is constant and cannot recover their
cellular areas.

### Proof

The endpoint claim is immediate. The \(n\times n\) grid filling is a disk with \(n^2\) cells, and
the signed-area lower bound proves it is minimal. All disks are homeomorphic, while their declared
cell counts differ.

## 3. Consequence for universal law fields

A space-valued matching theory can detect:

- empty realization fibres;
- noncontractible realization fibres;
- higher homotopy ambiguity.

It cannot, without enrichment, detect:

- based simple-homotopy or determinant torsion erased by derived equivalence;
- minimum filling cost erased by unweighted homotopy type;
- source dependence of the weak-equivalence doctrine.

Therefore a universal law field cannot consist only of homotopy types and matching maps. It needs
at least a structured realization object retaining some combination of:

1. cofibrations or elementary proof-cell attachments;
2. a declared weak-equivalence doctrine;
3. determinant or \(K\)-theory memory;
4. quantitative filling weights.

This is a forcing statement, not a proposed final ontology.

## 4. Sharp boundary

The theorem does not say homotopy theory is irrelevant. It says ordinary derived/homotopy
localization is a lossy observer. A richer Waldhausen, simple-homotopy, filtered, or
cost-enriched higher category may retain the missing data.

Conversely, if determinant and filling data are not source-invariant under the admissible
presentation moves, the enrichment must be discarded rather than promoted.

