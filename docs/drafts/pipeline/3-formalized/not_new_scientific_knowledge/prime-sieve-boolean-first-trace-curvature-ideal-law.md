# Prime-sieve Boolean first-trace curvature ideal law

- **ID:** `prime-sieve-boolean-first-trace-curvature-ideal-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL ALGEBRAIC CONNECTION-CURVATURE THEOREM
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/prime-sieve-boolean-first-trace-connection-curvature.md`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/PrimeSieveBooleanFirstTraceConnection.lean`

## Exact theorem

Let \(R,A,B\) be commutative rings, with \(A\) and \(B\) commutative \(R\)-algebras.  For
\(x,e\in A\) and \(r\in R\), define
\[
 \nabla(x,e;r)
 =
 (1-r)xe-x+x(1-e).
\tag{1}
\]
Then
\[
 \boxed{\nabla(x,e;r)=-rxe.}
\tag{2}
\]

For \(f\in A\) and \(t\in R\), define the two-order curvature
\[
\begin{aligned}
 \Omega(x;e,f;r,t)
 &=
 \nabla(x,e;r)+\nabla((1-r)xe,f;t)\\
 &\quad-\nabla(x,f;t)-\nabla((1-t)xf,e;r).
\end{aligned}
\tag{3}
\]
The exact factorization is
\[
 \boxed{
 \Omega(x;e,f;r,t)
 =
 t\,xf(1-e)-r\,xe(1-f).
 }
\tag{4}
\]
Consequently
\[
 \Omega(x;e,f;r,t)\in(1-e,1-f).
\tag{5}
\]
For every \(R\)-algebra map \(\varphi:A\to B\) satisfying
\[
 \varphi(e)=\varphi(f)=1,
\]
one has
\[
 \varphi(\Omega(x;e,f;r,t))=0.
\tag{6}
\]

## Meaning

Equation `(2)` is the universal algebra behind the prime-sieve cancellation
\[
 a_{P\cup\{p\}}D_{P\cup\{p\}}-a_PD_P+a_PD_P(1-D_p)
 =
 -{a_P\over p}D_{P\cup\{p\}}.
\]
Equation `(5)` proves that path curvature is not an arbitrary error: it is supported on the two
finite face constraints.  This is the finite algebraic model of the desired co-Poisson
mate-curvature ideal landing.  It neither supplies the all-prime extension nor identifies the
finite face ideal with the Xi co-Poisson ideal.

## Lean certificate

```text
firstTraceCorrectedEdge
firstTraceCorrectedEdge_eq
firstTraceCorrectedSquareCurvature
firstTraceCorrectedSquareCurvature_eq
firstTraceFaceDefectIdeal
firstTraceCorrectedSquareCurvature_mem_faceDefectIdeal
map_firstTraceCorrectedSquareCurvature_eq_zero
```

Direct verification:

```text
lake env lean GaloisForLFunctions/RHTower/PrimeSieveBooleanFirstTraceConnection.lean
```

## Hostile audit

1. The theorem is elementary commutative algebra and carries no novelty claim.
2. Ideal landing is finite and algebraic; it does not prove cofinal convergence of a primitive.
3. Mapping both faces to one is a constraint specialization, not a theorem that Xi zeros produce
   such a specialization.
4. No Gamma, Meyer, Contou--Carrère, Sonin, divisor, or positivity structure occurs in the Lean
   statement.
5. Its frontier value is diagnostic: nonzero prime-ordering curvature forces the next source
   comparison to live in categorical degree two.

## Gates

- [x] exact paper proof
- [x] exact Lean formalization
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [ ] all-prime two-cell
- [ ] cofinal primitive
- [ ] literal Xi co-Poisson/Sonin landing
- [ ] RH
