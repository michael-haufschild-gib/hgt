# The elliptic-gamma QFT arithmetic closure horizon

- **ID:** `elliptic-gamma-qft-arithmetic-closure-horizon`
- **Stage:** 1-in-progress
- **Type:** CLASSIFICATION CONJECTURE / DIFFERENTIAL ALGEBRA / EXACT QFT APPLICATION
- **Scientific status:** `[CONJECTURE: COMPLETE DICHOTOMY] [INDEPENDENT PHASE PAPER-PROVEN] [FULL LEAN OPEN] [NOVELTY PROVISIONAL]`
- **Methods:** symbolic proof, primary-source novelty audit, and unconditional Lean formalization;
  no numerical computation
- **Working title:** *The Hypertranscendental Holographic Horizon: Arithmetic Closure in a
  Four-Dimensional Quantum Field Theory*

## Claim

Let `p,q` be nonzero complex nomes with `|p|,|q|<1`, and let

```text
Gamma(x;p,q)=product_(j,k>=0) (1-p^(j+1)q^(k+1)/x)/(1-x p^j q^k)
```

be the elliptic gamma function.  As a meromorphic function of an additive chemical potential `z`,
with `x=exp(2 pi i z)`, the proposed complete classification is

```text
Gamma(-;p,q) is differentially algebraic over C(z)
  iff p and q are multiplicatively dependent;

Gamma(-;p,q) is hypertranscendental over C(z)
  iff p and q are multiplicatively independent.                 (1)
```

In the independent phase, choose logarithms `p=exp(2 pi i tau)` and
`q=exp(2 pi i sigma)`.  Then `1,tau,sigma` are `Q`-independent and the stronger theorem from
`elliptic-gamma-rank-three-da-spectrum` applies: the DA translation spectrum of the logarithmic
derivative is exactly

```text
H_3=Z+Z tau+Z sigma,
```

and the differential transcendence degree of every finite defect family is the number of distinct
nonzero shift cosets in `C/H_3`.

Thus the binary classification `(1)` is only the first layer.  The independent phase carries an
exact orbit-resolved differential matroid that reconstructs the equivalence relation modulo the
rank-three period subgroup.

## Hausdorff--Kolchin correspondence `[CONJECTURE: HEADLINE FORM]`

Let `H_3=Z+Z tau+Z sigma` and give `C/H_3` the quotient topology.  For upper-half-plane `tau,sigma`,
the complete classification `(1)` is equivalent to

```text
Gamma(-;tau,sigma) is DA  iff C/H_3 is Hausdorff,             (2a)
Gamma(-;tau,sigma) is HT  iff C/H_3 is non-Hausdorff.         (2b)
```

Indeed, rational dependence of `1,tau,sigma` makes `H_3` a discrete lattice contained in a finite
rescaling of `Z+Z tau`, hence closed.  Rational independence makes it a rank-three integer subgroup
of the two-real-dimensional plane; it is nondiscrete and not closed, so the ordinary quotient is
non-Hausdorff.  Conversely, the quotient by an additive subgroup is Hausdorff exactly when the
subgroup is closed.

Felder--Henriques--Rossi--Zhu already replace the non-Hausdorff quotient by the triptic stack and
construct the gamma gerbe on it.  That topology is therefore parent theory.  The candidate new
content is the **Hausdorff--Kolchin correspondence**: the topological separation defect of the
large-gauge quotient is equivalent to the impossibility of every finite algebraic differential law
for its canonical QFT section, with the full defect matroid retaining the orbit-resolved data.

The quotient is a chemical-potential/large-gauge moduli object, not physical spacetime.  Calling
`(2)` a black-hole event horizon or a thermodynamic transition would be false.  The permitted
physical statement is that an exactly defined protected QFT trace detects Hausdorff failure in its
background moduli stack through hypertranscendence.

## Dependent phase `[PAPER PROOF] [KNOWN FACTORIZATION INPUT]`

Suppose `p^m=q^n=P` for positive integers `m,n`.  Partition the two product indices by residues
modulo `m,n`.  Felder--Varchenko's multiplication lemma gives the exact identity

```text
Gamma(x;p,q)=product_(0<=a<m,0<=b<n) Gamma(x p^a q^b;P,P).        (2)
```

For completeness, the numerator reindexing is

```text
(a,b) -> (m-1-a,n-1-b),
```

because

```text
p q p^(m-1-a) q^(n-1-b)/x=P^2/(x p^a q^b).
```

Kato proves that the equal-period elliptic gamma is differentially algebraic.  Translations and
finite products preserve differential algebraicity, so `(2)` proves the dependent implication in
`(1)`.  The factorization is classical and is not claimed as new knowledge.

## Independent phase `[PAPER-PROVEN IN PARENT CARD]`

Multiplicative independence is equivalent to `Q`-independence of `1,tau,sigma`.  The parent theorem
proves hypertranscendence by a paired noncommensurable-elliptic-curve obstruction and strengthens it
to the exact rank-three defect matroid.  Kato explicitly left non-rational periods open.  Searches
through current elliptic difference-Galois, summability, gamma-gerbe, and QFT-index literature have
not located the dichotomy `(1)` or the defect-matroid refinement.

The independent direction remains provisional until its paired telescoping and analytic-field
assembly are independently checked and formalized unconditionally in Lean.

## Exact QFT meaning

The elliptic gamma function is the superconformal index of a free four-dimensional `N=1` chiral
multiplet.  The variables `p,q` encode rotations/chemical potentials of the supersymmetric
background.  Therefore `(1)` is literally a theorem about an exactly solvable quantum field theory:
commensurability of the background twists decides whether its protected partition function admits
any finite algebraic differential law in the chemical potential.

In the independent phase, no finite nonlinear differential closure exists, and shifted responses
belonging to distinct triptic cosets are differentially algebraically independent.  This is the
precise content of the phrase **hypertranscendental holographic horizon**: local differential
observables recover a global rank-three quotient through the pattern of which translation defects
can and cannot close.

Equivalently, the theorem says that the protected BPS trace of this four-dimensional theory has no
polynomial relation involving any finite collection of its ordinary chemical-potential derivatives.
It still obeys global difference, modular, and cocycle constraints.  The point is exactly that the
theory is fixed by those global constraints and not generated by a finite differential flow.

## Finite free-chiral matter theorem `[CONJECTURE: PHYSICAL PROMOTION OF THE TRIPTIC INVARIANT]`

For a finite integer divisor `D=sum_g n_g[g]` on `C/H_3`, choose lifts `a_g` and form

```text
Z_D(z)=product_g Gamma(z+a_g;tau,sigma)^(n_g).               (3)
```

This is the protected partition function of a finite collection of unit-charge free chiral
building blocks and their inverse contributions.  The triptic reciprocity and translation-module
cards predict the exact classification

```text
Z_D is DA  iff D=0 in Z[C/H_3],                              (4)

dtrdeg { Z_D(z+h_i)/Z_D(z) }_i
  = dim_C span { (t_(h_i+H_3)-1)D }_i.                       (5)
```

For an honest product with only positive multiplicities, `D` cannot vanish, so every nonempty
finite free-chiral matter index is hypertranscendental in the independent phase.  Signed products
can close differentially only by exact cancellation in the triptic quotient, not merely by
cancellation of total degree.

The ordinary multiplicative cocycle and its degree are established gerbe/line-bundle data.  The
candidate new physical invariant is the full labelled orbit divisor and its differential matroid.
Its augmentation recovers only a coarse total charge; nonzero augmentation-zero divisors remain
hypertranscendental.  No identification with the complete four-dimensional 't Hooft anomaly
polynomial is claimed without a separate charge-dependent modular calculation.

For one free chiral, the exact DA spectrum

```text
{h : the shifted logarithmic response at h is DA}=H_3        (6)
```

is a local-to-global reconstruction theorem: the pattern of finite differential closure recovers
the large-gauge period subgroup itself.  This is the literal holographic statement supported by
the mathematics.

This is an arithmetic closure transition, not presently a thermodynamic phase transition.  The
index remains analytic in `p,q` away from its ordinary divisor.  No experimental signature, black
hole theorem, or quantum-gravity claim follows from `(1)` alone.

## Anti-theatre attacks

1. The QFT identification of the elliptic gamma function is standard and contributes significance,
   not mathematical novelty.
2. Felder--Varchenko's factorization and Kato's dependent-period DA theorem are established parents.
3. Gamma-gerbe theory already identifies the triptic quotient and its cocycle.  Novelty can only
   survive in the differential-algebraic classification, exact spectrum, and defect matroid.
4. Calling DA versus HT a phase transition would overstate the physics unless a nonanalytic physical
   observable is found.  The permitted term is **arithmetic closure transition**.
5. A theorem only about one named special function is not Fields-Medal scale.  The rank-three
   mixed-constraint class, cross-curve reciprocity, and complete orbit-resolved invariant are the
   necessary broader layer.
6. Abstract group-algebra shells do not count as formalization of the theorem.  The actual product,
   meromorphic field, paired increment identities, telescoping descent, and DA/HT conclusion must
   all be unconditional in Lean.

## RH impact

The classification does not imply RH.  Its useful impact is methodological: it gives a fully
structured example in which a rank-three global constraint, rather than a differential flow,
forces hypertranscendence and exposes an exact translation-defect matroid.  An RH application would
need an independently constructed completed-zeta constraint whose defect invariant detects
horizontal zero location.  No such bridge is presently proved.

## Gates

- [x] Exact dependent-period factorization proved on paper and identified as classical.
- [x] Kato boundary checked from the primary paper.
- [x] Independent-period theorem and exact matroid stated and paper-proved in the parent card.
- [x] Preliminary exact/equivalent/stronger literature search through 2026.
- [x] Exact free-chiral QFT interpretation located in primary physics literature.
- [x] Thermodynamic/black-hole overclaim explicitly excluded.
- [x] Residue reindexing and numerator reversal of the actual double product formalized
  unconditionally in Lean as a flattened finite-family product.
- [ ] Finite-family Fubini regrouping formalized to identify the flattened product with the literal
  finite product of equal-nome elliptic gamma functions.
- [ ] Kato equal-period algebraic differential equation formalized unconditionally in Lean.
- [ ] Independent-period paired theorem formalized unconditionally in Lean.
- [ ] Full iff theorem assembled in Lean with axiom audit.
- [x] Independent rank-three subgroup nonclosedness and non-Hausdorff quotient formalized
  unconditionally in Lean (`RankThreePeriodNonHausdorff`).
- [x] Closedness/Hausdorffness formalized unconditionally when the period group is contained in a
  genuine rank-two real lattice (`RankThreePeriodNonHausdorff`); the arithmetic specialization from
  commensurable nomes to this containment remains to be assembled.
- [ ] Hausdorff--Kolchin equivalence `(2)` assembled in Lean.
- [ ] Finite free-chiral matter classification `(4)--(5)` formalized on the actual product.
- [ ] Independent expert audit in elliptic difference Galois theory and gamma gerbes.
- [ ] Broader mixed-constraint/triptic reciprocity theorem passes the Fields-Medal significance gate.
