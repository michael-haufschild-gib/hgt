# Finite Boolean Hochschild diagonals are uniformly contractible but cofinally nonconvergent

- **ID:** `finite-boolean-hochschild-diagonal-cofinal-fracture`
- **Stage:** 3-formalized
- **Type:** PARENT-THEORY CLOSURE / EXACT INFINITY FRACTURE
- **Scientific status:** `[PAPER-PROVED] [NOT NEW IN LITERATURE] [NOT RH]`
- **Parent in corpus:**
  `formal/GaloisForLFunctions/HTGeometry/LowDegreeHochschildFaceFlatness.lean`.
- **Role:** closes the purely Boolean higher-homotopy part of
  `XI_CONTROLLED_CUBICAL_HOMOTOPY_BASE_CHANGE`; isolates strict all-prime convergence, the
  Gamma/first-trace attachment, and Xi boundary landing as the remaining work.

## 1. Canonical finite-prime diagonal

Let \(P\) be finite, let
\[
 \Omega_P=\{\pm1\}^{P},
 \qquad
 A_P=C(\Omega_P)
\]
with the supremum norm and pointwise multiplication, and let
\(\delta_\omega\) be the atomic idempotents.  Define
\[
 D_P
 =
 \sum_{\omega\in\Omega_P}
 \delta_\omega\otimes\delta_\omega
 \in A_P\widehat\otimes_\pi A_P.
\tag{1}
\]
Then
\[
 m(D_P)=1,
 \qquad
 (a\otimes1)D_P=D_P(1\otimes a)
 \quad(a\in A_P).
\tag{2}
\]
Thus \(D_P\) is the separability diagonal of the finite Boolean algebra.

Use the Walsh characters of the finite group \(\Omega_P\).  Fourier inversion gives
\[
 D_P
 =
 2^{-|P|}
 \sum_{\chi\in\widehat{\Omega_P}}
 \chi\otimes\overline\chi.
\tag{3}
\]
Every character has supremum norm one, so `(3)` gives
\[
 \|D_P\|_\pi\leq1.
\]
The multiplication map
\(m:A_P\widehat\otimes_\pi A_P\to A_P\) is contractive and \(m(D_P)=1\), hence
\[
 \boxed{\ \|D_P\|_\pi=1\ }
\tag{4}
\]
for every finite \(P\).  No dimension factor occurs.

## 2. All-degree dimension-free Hochschild contraction

On the projective Hochschild chains
\[
 C_n(A_P)=A_P^{\widehat\otimes_\pi(n+1)}
\]
write \(D_P=\sum_i x_i\otimes y_i\) and define
\[
 s_n(a_0\otimes\cdots\otimes a_n)
 =
 \sum_i
 x_i\otimes y_i a_0\otimes a_1\otimes\cdots\otimes a_n.
\tag{5}
\]
The diagonal relations `(2)` give the standard identity
\[
 b_{n+1}s_n+s_{n-1}b_n
 =
 \operatorname{id}_{C_n(A_P)}
 \qquad(n\geq1).
\tag{6}
\]
Indeed, in \(b_{n+1}s_n\) the first face is
\(\sum_i x_iy_i a_0\otimes\cdots=a_0\otimes\cdots\); the internal faces cancel those of
\(s_{n-1}b_n\) with alternating signs; and the cyclic last face cancels by the centralizing
identity in `(2)`.

Projective crossnorm multiplicativity and `(4)` give
\[
 \boxed{\ \|s_n\|\leq1\quad\text{for every }n\text{ and every finite }P.\ }
\tag{7}
\]
Therefore every positive-degree Boolean Hochschild cycle has a canonical filler with no growth
in homological degree or number of primes.  The explicit two-face primitive in
`LowDegreeHochschildFaceFlatness.lean` is the first nontrivial coordinate expression of this
all-degree separability contraction.

For disjoint \(P,Q\), the natural shuffle identification gives
\[
 D_{P\sqcup Q}=D_P\otimes D_Q.
\tag{8}
\]
Hence the diagonals are multiplicative under independent prime packets.  Purely finite Boolean
incidence, braid coherence, and higher cubical faces do not generate an essential singularity.

## 3. Exact cofinal fracture

Uniform norm does not imply a strict all-prime limit.  Add one Boolean coordinate \(q\notin P\)
and identify
\[
 A_{P\cup\{q\}}=A_P\widehat\otimes_\varepsilon A_{\{q\}}.
\]
The unit-extension of the old diagonal and the new diagonal are, after the canonical tensor
shuffle,
\[
 \widetilde D_P=D_P\otimes(1\otimes1),
 \qquad
 D_{P\cup\{q\}}=D_P\otimes D_{\{q\}}.
\tag{9}
\]
For the two-point algebra, with nontrivial Walsh character \(u\),
\[
 D_{\{q\}}=\frac12(1\otimes1+u\otimes u),
\]
and therefore
\[
 D_{\{q\}}-1\otimes1
 =
 \frac12(u\otimes u-1\otimes1).
\tag{10}
\]
The right side has projective norm at most one.  Its image in the injective tensor product is
the function on \(\{\pm1\}^2\) which is zero on the diagonal and \(-1\) off the diagonal, so its
injective norm is one.  Since the injective norm is bounded by the projective norm,
\[
 \|D_{\{q\}}-1\otimes1\|_\pi=1.
\tag{11}
\]
Using the projective crossnorm on the pure outer tensor and `(4)`,
\[
 \boxed{\quad
 \|D_{P\cup\{q\}}-\widetilde D_P\|_\pi=1.
 \quad}
\tag{12}
\]
Thus the canonical finite-prime contractions are bounded but not Cauchy under prime enlargement.
No strict diagonal appears in the ordinary all-prime projective tensor completion.  A bounded
approximate or virtual diagonal can survive in a weaker/bidual completion, but that weakening is
not an essential sewing mechanism.

## 4. Consequence for the RH architecture

The finite algebraic part of `XI_CONTROLLED_CUBICAL_HOMOTOPY_BASE_CHANGE` is now classified:

```text
finite Boolean/Kummer cube:
  all positive Hochschild degrees contract with norm <= 1;

adding one prime:
  canonical diagonal changes by exact projective distance 1;

all-prime ordinary projective completion:
  no strict limit of the canonical contractions;

virtual/bidual completion:
  may retain a bounded diagonal, but remains finite-Rees and cannot sew the
  actual all-orders-flat/half-normal Wold fracture;

remaining possible bridge:
  essential Gamma/first-trace renormalization of the nonconvergent diagonal,
  followed by one strict source-defined Xi conormal boundary map.
```

The arbitrary-dimensional Rees theorem therefore does not point toward larger Boolean matrices.
It says the bounded virtual diagonal is categorically too regular.  The missing object must keep
the nonconvergent finite diagonals and the essential Wold--Gamma exponential record together,
while retaining the same pointed Xi conormal through the boundary observation.

This does not prove that such a renormalized diagonal exists or that its Xi specialization
conserves the source modular exponent.  It removes “construct unspecified higher finite
homotopies” from the open core and leaves three exact obligations:

1. attach the Wold first-trace/Gamma essential record to `(5)` compatibly with `(8)`;
2. form a strict all-prime Tate/irregular totalization despite `(12)`; and
3. prove the Gamma/co-Poisson/Sonin Xi boundary class is the specialization of that same
   renormalized diagonal, with every multiplicity jet nonzero.

## 5. Literature boundary

Finite-dimensional commutative \(C^*\)-algebras are contractible/amenable Banach algebras; their
separability diagonals and the induced Hochschild contractions are classical.  The norm-one
Fourier representation `(3)` is the standard amenability diagonal of a finite abelian group
written in the function algebra.  Infinite \(C(X)\) algebras have bounded approximate/virtual
diagonals but no actual separability diagonal unless the spectrum is finite.

No novelty is claimed for `(1)`--`(12)`.  Corpus gain is the exact diagnosis that finite higher
prime coherence is uniformly controlled while its canonical diagonals fail strict cofinal
convergence by a fixed amount; this locates the RH-bearing infinity problem after, not inside,
finite cubical homotopy.

## 6. Lean formalization

Formal artifact:
`formal/GaloisForLFunctions/HTGeometry/FiniteBooleanHochschildDiagonal.lean`.

The module proves, for every finite coordinate type, the atomic separability diagonal,
multiplication and centrality laws, Walsh expansion, exact projective norm one, genuine
all-degree Hochschild chain contraction identity, projective operator norm at most one,
disjoint-packet multiplicativity, exact two-point fracture, singleton-coordinate shuffle
factorization, and exact arbitrary-packet cofinal fracture norm one.  It is imported by
`GaloisForLFunctions.HTGeometry`.

Targeted audit:

- `lake build GaloisForLFunctions.HTGeometry.FiniteBooleanHochschildDiagonal` passes;
- all ten theorem endpoints report only Lean's standard `propext`, `Classical.choice`, and
  `Quot.sound` axioms;
- formal lint reports no prohibited declaration in this module.

The remaining Wold/Gamma, all-prime irregular totalization, and Xi-specialization items below
are explicitly downstream research obligations, not unformalized premises of equations
`(1)`--`(12)`.

## 7. Gates

- [x] finite Boolean separability diagonal constructed
- [x] exact projective norm one proved
- [x] all-degree Hochschild contraction proved
- [x] dimension-free contraction bound proved
- [x] multiplicativity under disjoint prime packets proved
- [x] exact one-prime cofinal jump proved
- [x] parent-theory status recorded
- [ ] Wold/Gamma essential renormalization of the diagonal
- [ ] strict all-prime Tate/irregular totalization
- [ ] multiplicity-faithful Xi boundary specialization
- [ ] RH
