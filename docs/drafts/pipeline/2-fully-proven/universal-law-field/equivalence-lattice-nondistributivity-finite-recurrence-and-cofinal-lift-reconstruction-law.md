# Equivalence-lattice nondistributivity, finite recurrence, and cofinal lift reconstruction law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [UNIVERSAL-LAW FIELD]
  [DYNAMIC-EQUIVALENCE FORK] [NON-DISTRIBUTIVE LOCALIZATION]
  [FINITE RECURRENCE/OPEN LIFT] [COFINAL RECONSTRUCTION] [NOT RH] [NO LEAN]

## 1. Equivalence doctrines

For a set \(X\), let \(\operatorname{Eq}(X)\) be the lattice of equivalence relations on \(X\),
ordered by inclusion. A relation \(E\) is interpreted as an **observer doctrine**: the observer
retains \(X/E\) and declares \(E\)-equivalent source states indistinguishable.

Meets are intersections. Joins are equivalence closures of unions.

## 2. Nondistributive law

### Theorem 2.1 — observer doctrines do not form a classical Boolean geometry

For \(X=\{1,2,3\}\), define

\[
 \alpha=12|3,\qquad \beta=13|2,\qquad \gamma=1|23.
\tag{ED.1}
\]

Then every pair of distinct relations among \(\alpha,\beta,\gamma\) has equality relation
\(\Delta\) as meet and indiscrete relation \(\nabla\) as join. Consequently

\[
 \alpha\wedge(\beta\vee\gamma)=\alpha,
 \qquad
 (\alpha\wedge\beta)\vee(\alpha\wedge\gamma)=\Delta.
\tag{ED.2}
\]

Thus \(\operatorname{Eq}(X)\) is nondistributive.

### Consequence

There is no universal set-theoretic law that decomposes “information retained jointly by two
observer doctrines” into independent pieces. Combining identifications is intrinsically
non-Boolean even before topology, probability, or curvature enters.

## 3. Finite recurrence and cofinal reconstruction

Let \(X=\mathbb Z\), let \(T(n)=n+1\), and for \(m\geq2\) let

\[
 n\,E_m\,n' \Longleftrightarrow n\equiv n'\pmod m.
\tag{ED.3}
\]

### Theorem 3.1 — every finite doctrine sees closed recurrence

On \(X/E_m\cong\mathbb Z/m\mathbb Z\), the induced history is periodic with exact period \(m\).
For any finite set \(F=\{m_1,\ldots,m_r\}\), the joint observer

\[
 q_F:\mathbb Z\longrightarrow\prod_{m\in F}\mathbb Z/m\mathbb Z
\tag{ED.4}
\]

is periodic with period

\[
 L_F=\operatorname{lcm}(m_1,\ldots,m_r).
\tag{ED.5}
\]

It has infinite fibres and therefore cannot reconstruct lifted history.

### Theorem 3.2 — the cofinal doctrine family reconstructs the open lift

The full map

\[
 q_\infty:\mathbb Z\longrightarrow\prod_{m\geq2}\mathbb Z/m\mathbb Z
\tag{ED.6}
\]

is injective. Equivalently,

\[
 \bigcap_{m\geq2}E_m=\Delta.
\tag{ED.7}
\]

Hence every finite observer family sees a closed periodic history, while the cofinal family
reconstructs the nonperiodic lifted translation \(n\mapsto n+1\) on \(\mathbb Z\).

### Proof

The finite quotient statements are immediate from modular addition. If \(q_\infty(n)=q_\infty(n')\),
then \(d=n-n'\) is divisible by every integer \(m\geq2\). Taking \(m>|d|\) forces \(d=0\).

## 4. Positive phase quotient as another doctrine

On \(X=\mathbb C^\times\), define

\[
 z\,E_{\mathrm{ph}}\,w
 \Longleftrightarrow |z|=|w|.
\tag{ED.8}
\]

Then \(X/E_{\mathrm{ph}}\cong\mathbb R_{>0}\). Every phase loop \(e^{it}\) becomes the constant
positive history \(1\), while its universal-cover lift remains open when it has nonzero winding.
Positivity is therefore one possible equivalence doctrine, not a universal consequence of being
positive.

## 5. Native coupling

One elementary field couples four phenomena:

1. observer doctrines form a nondistributive lattice;
2. each finite doctrine family produces exact recurrence;
3. the source lift remains open;
4. only a cofinal separating doctrine family reconstructs it.

No matching map, differential connection, or filling cost is used.

## 6. Fatal boundaries

1. The set of admissible equivalence doctrines must be source-defined. Arbitrary partitions can
   manufacture any desired phenomenon.
2. The lattice \(\operatorname{Eq}(X)\) is too large to be a field by itself. Composition,
   admissibility, topology, cost, and dynamics need constitutive laws.
3. Cofinal separation does not imply a useful completion or continuous reconstruction.
4. Congruence observers are a calibration, not evidence that all theorem observers are quotients
   of one set.
5. If the corpus admits one finite faithful observer doctrine, the finite-recurrence/open-lift
   mechanism above is irrelevant.

## 7. Distinguishing prediction

If dynamic equivalence is fundamental, some proof-route incompatibilities should be caused by
nondistributivity of their localization doctrines rather than by empty realization fibres or large
proof fillings. A successful field must derive an admissible doctrine lattice whose finite
localizations recur but whose cofinal intersection is source-faithful.

