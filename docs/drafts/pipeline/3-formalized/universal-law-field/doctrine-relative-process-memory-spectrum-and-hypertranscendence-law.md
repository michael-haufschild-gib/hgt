# Doctrine-relative process-memory spectrum and hypertranscendence law

- **ID:** ULF-DRMS-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FIELD-LEVEL PHASE CLASSIFICATION
- **Source:** infinite-memory gate for Constitutive Process Mathematics
- **Statement:** Constant-coefficient response memory, base-dependent linear memory, nonlinear algebraic differential memory, and hypertranscendental memory are four distinct process phases; complexity can collapse when the admitted intervention doctrine is enlarged.
- **Status:** [PAPER-PROVED] [FIELD-LEVEL MEMORY SPECTRUM] [STRICT PHASE SEPARATION] [CLASSICAL HANKEL/ODE/KOLCHIN PARENTS] [NOT RH] [LEAN CERTIFIED]

## 1. Setup

Let \(K=\mathbb C(z)\) with derivation \(D=d/dz\), and let \(f\) be a nonzero analytic germ at
\(z=0\), embedded in a differential field of meromorphic germs. Put

\[
m_n=f^{(n)}(0),
\qquad
H_N(f)=(m_{i+j})_{0\le i,j\le N}.
\tag{1}
\]

We attach three memory measurements to the same germ.

1. Its **constant-response memory** is
   \[
   r_{\mathrm{cc}}(f)=\sup_N\operatorname{rank}_{\mathbb C}H_N(f).
   \tag{2}
   \]
2. Its **base-aware linear memory** is
   \[
   r_{\mathrm{lin}}(f)=
   \dim_K\operatorname{span}_K\{D^nf:n\ge0\}.
   \tag{3}
   \]
3. Its **algebraic intervention profile** is
   \[
   h_f(N)=\operatorname{trdeg}_K K(f,Df,\ldots,D^Nf).
   \tag{4}
   \]

These invariants use successively richer processor doctrines: constant linear recurrence,
base-dependent linear recurrence, and arbitrary algebraic differential closure.

## 2. Constant-response memory

### Theorem 2.1

The following are equivalent.

1. \(r_{\mathrm{cc}}(f)<\infty\).
2. The response sequence \((m_n)\) satisfies a nonzero constant-coefficient recurrence.
3. The germ satisfies a nonzero constant-coefficient linear differential equation.
4. Near \(0\),
   \[
   f(z)=\sum_{j=1}^s P_j(z)e^{\lambda_jz}
   \tag{5}
   \]
   for polynomials \(P_j\) and constants \(\lambda_j\in\mathbb C\).

### Proof

Finite rank of the infinite Hankel matrix means that a minimal initial family of columns becomes
linearly dependent. Minimality makes the last coefficient nonzero, so there are constants
\(a_0,\ldots,a_{r-1}\) such that

\[
m_{n+r}+a_{r-1}m_{n+r-1}+\cdots+a_0m_n=0
\qquad(n\ge0).
\tag{6}
\]

Conversely, (6) bounds every Hankel rank by \(r\). Define

\[
g=D^rf+a_{r-1}D^{r-1}f+\cdots+a_0f.
\]

Equation (6) says that every derivative of \(g\) vanishes at \(0\); analyticity gives \(g=0\) as a
germ. This proves equivalence of 1--3. The solution space of a constant-coefficient differential
operator is exactly the exponential-polynomial space (5), proving 4 and its converse. QED.

Thus finite Hankel memory is not generic finite process memory. It is finite memory for the
particularly restrictive doctrine that cannot use the base coordinate \(z\).

## 3. Base-aware linear and nonlinear algebraic memory

### Theorem 3.1

1. \(r_{\mathrm{lin}}(f)<\infty\) iff \(f\) satisfies a nonzero linear differential equation over
   \(K\).
2. \(f\) is differentially algebraic over \(K\) iff \(h_f(N)\) is bounded.
3. \(f\) is hypertranscendental over \(K\) iff
   \[
   \boxed{h_f(N)=N+1\quad\text{for every }N\ge0.}
   \tag{7}
   \]

### Proof

Finite \(K\)-linear span of the derivatives is exactly a \(K\)-linear dependence among finitely many
of them, which is a scalar linear differential equation. The converse follows by reducing higher
derivatives recursively.

If \(f\) is differentially algebraic, choose a differential relation of minimal order \(r\). In
characteristic zero, its separant in the highest derivative is nonzero. Differentiating the relation
expresses every derivative above order \(r\) algebraically over
\(K(f,\ldots,D^{r-1}f)\). Hence \(h_f(N)\le r\) for all \(N\). Conversely, boundedness of the
nondecreasing integer sequence \(h_f(N)\) forces algebraic dependence among a finite jet, which is
a differential polynomial relation.

Finally, failure of (7) at one stage is precisely algebraic dependence of a finite jet and hence
differential algebraicity. Its negation at every stage is hypertranscendence. QED.

## 4. Strict phase separation

The implications

\[
\boxed{
\text{constant-coefficient finite memory}
\Longrightarrow
\text{base-aware finite linear memory}
\Longrightarrow
\text{finite algebraic differential memory}
}
\tag{8}
\]

are strict.

### 4.1 Infinite Hankel memory with one-dimensional linear memory

Let \(f(z)=e^{z^2}\). Then \(Df=2zf\), so \(r_{\mathrm{lin}}(f)=1\). But

\[
m_{2n}=\frac{(2n)!}{n!},
\qquad
m_{2n+1}=0.
\tag{9}
\]

Every constant-coefficient recurrent sequence has at most polynomial-times-exponential growth.
Stirling's formula gives

\[
\left(\frac{(2n)!}{n!}\right)^{1/(2n)}\longrightarrow\infty,
\]

so (9) satisfies no such recurrence. Every derivative of \(f\) is a polynomial multiple of \(f\),
and \(f\) is transcendental over \(K\) because it has an essential singularity at infinity.
Therefore

\[
r_{\mathrm{cc}}(e^{z^2})=\infty,
\qquad
r_{\mathrm{lin}}(e^{z^2})=1,
\qquad
h_{e^{z^2}}(N)=1.
\tag{10}
\]

### 4.2 Finite nonlinear memory without finite linear memory

Let \(f(z)=\tan z\). It satisfies

\[
Df=1+f^2,
\tag{11}
\]

All higher derivatives are polynomials in \(f\), and \(f\) is transcendental over \(K\) because it
has infinitely many poles. Thus \(h_f(N)=1\). It is not D-finite over \(K\): a solution of a
rational-coefficient linear ODE can have finite singularities only among the finite singular set of
its coefficients and leading term, whereas the meromorphic continuation of \(\tan z\) has infinitely
many poles. Hence \(r_{\mathrm{lin}}(\tan z)=\infty\).

### 4.3 Maximal algebraic intervention memory

The germ \(f(z)=\Gamma(z+1)\) is analytic at \(0\) and hypertranscendental over \(K\) by Hölder's
theorem and translation invariance of differential algebraicity. Therefore

\[
h_f(N)=N+1
\qquad(N\ge0).
\tag{12}
\]

These examples prove that no single scalar called "process rank" can represent all four memory phases.

## 5. Doctrine-relative memory spectrum

The exact invariant is the ordered fingerprint

\[
\mathfrak M(f)=
\bigl(r_{\mathrm{cc}}(f),\ r_{\mathrm{lin}}(f),\ (h_f(N))_{N\ge0}\bigr),
\tag{13}
\]

together with the declared processor doctrine. Increasing the legal operations can compress an
apparently infinite process:

- adjoining the base coordinate compresses \(e^{z^2}\) from infinite constant memory to one linear
  state;
- allowing nonlinear algebraic update compresses \(\tan z\) from infinite linear memory to one
  algebraic state;
- no finite algebraic differential processor compresses a hypertranscendental germ.

This gives Constitutive Process Mathematics a field-level principle:

\[
\boxed{
\text{law complexity is relative to the algebra of admitted interventions.}}
\tag{14}
\]

The invariant object is a memory spectrum over intervention doctrines, not a preferred numerical
rank.

## 6. Relation to topology, recurrence, and history

Equation (12) means that every new derivative contributes one algebraically independent direction.
Under the formally smooth split hypotheses of the existing Kolchin--Spencer theorem, the inverse
jet realization is therefore nonlocally compact and every finite observer misses an infinite tail.
This is the exact sense in which hypertranscendence produces noncompactness.

It does **not** imply that an observed dynamical orbit is noncompact. Finite exponential-polynomial
processes can have recurrent unitary realizations with open marked phase lifts, while separately an
HT process may have a compact observed realization. Orbit recurrence, dilation history, and
differential memory are different coordinates of a constitutive process.

## 7. Field consequences and predictions

1. Any proposed universal complexity that identifies infinite Hankel rank with HT is false by
   \(e^{z^2}\).
2. Any proposed finite-state theorem must state which update algebra is legal: constant, rational
   linear, algebraic, analytic, or arbitrary.
3. A proof route can look infinite in one chart and finite in another without contradiction. The
   change of doctrine is itself constitutive data and must be represented by a comparison functor.
4. CPM's HT sector should be modeled by the full growth function \(h_f\), not by one determinant,
   one orbit closure, or one completion rank.
5. A genuine cross-doctrine theorem must preserve the memory fingerprint or explicitly compute how
   it contracts under doctrine enlargement.

## 8. Hostile scope

- Hankel, ODE, D-finite, and Kolchin ingredients are classical.
- New use here is their organization as one doctrine-indexed process-memory spectrum.
- The theorem concerns one derivation and one analytic germ. Partial differential, difference,
  noncommutative, and higher-process versions remain open.
- Formal smoothness is required before maximal jet growth is interpreted as a topological
  noncompactness theorem.
- No physical cost, entropy, source selection, RH statement, or whole-corpus realization follows.

## Corpus parents

- `operator-presentation-bounded-innovation-stabilization.md` supplies the exact linear/nonlinear
  differential-state boundary and the `tan` counterexample.
- `hypertranscendental-phase-infinite-topological-charge-rank.md` supplies the finite-translation
  rank/exponential-polynomial theorem and its DA infinite-rank anti-converse.
- `kolchin-spencer-inverse-limit-noncompactness-and-observer-tail-law.md` supplies the conditional
  topological realization of maximal jet growth.
- `atomic-differential-operator-three-realization-process-law.md` supplies the finite reconstructive
  chamber from which this infinite hierarchy departs.

## Log

- 2026-08-09 — four process-memory phases separated; \(e^{z^2}\), \(\tan z\), and shifted Gamma fixed
  as strict witnesses; doctrine-relative memory spectrum promoted as CPM's infinite-memory invariant.

## Lean certification status

**COMPLETE.**  Modules `GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum`
(§§1–2) and `GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemoryWitnesses` (§§3–5), both
wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.

- **Theorem 2.1** — `seqConstantRecurrence_iff_bddHankelRank` (clauses 1 ⟺ 2),
  `seqConstantRecurrence_respSeq_iff_germConstantODE` (2 ⟺ 3),
  `germExpPoly_of_germConstantODE` and `germConstantODE_of_germExpPoly` (3 ⟺ 4), bundled as
  `constant_memory_tfae`.
- **Theorem 3.1, clause 1** — `linearMemory_iff_dFiniteOn`, with the `ℂ(z)`-span of the jets
  formalized denominator-cleared (`InJetSpan`, `LinearMemoryAtMost`) and its closure under
  differentiation proved as `InJetSpan.deriv_mem`.
- **Theorem 3.1, clauses 2 and 3** — `differentiallyAlgebraic_iff_exists_order'`,
  `hypertranscendental_iff_forall_not_order`, and equation (7) itself as
  `hypertranscendental_iff_algebraicIndependent_jets`: for an entire germ, hypertranscendence is
  exactly algebraic independence of `f, Df, …, D^N f` over `ℂ(z)` for every `N`, i.e.
  `h_f(N) = N + 1`.
- **§4.1** — `not_bddHankelRank_expSq`, `linearMemoryAtMost_expSq`,
  `differentiallyAlgebraicOfOrder_expSq`, `not_algebraicOn_expSq`.
- **§4.2** — `not_dFiniteOn_tan`, `differentiallyAlgebraicOn_tan`, `not_algebraicOn_tan`.
- **§4.3** — `hypertranscendental_gammaShift`, `not_differentiallyAlgebraicOfOrder_gammaShift`.
- **§5** — `doctrine_memory_spectrum` bundles the three witnesses; `dFiniteOn_of_bddHankelRank`
  certifies the first implication of (8).

`#print axioms` on every capstone reports only `propext`, `Classical.choice`, `Quot.sound`.

### Three proofs that changed in formalization

1. **Clause 1 ⇒ 2 (§2).**  The paper argues by "a minimal initial family of columns becomes
   linearly dependent".  Lean instead intersects the nested compact sets of unit candidate
   recurrence vectors satisfying the first `N` constraints (`recurrenceCandidates`,
   `exists_recurrence_vector`); this avoids choosing a minimal family and is where the bounded
   rank is used.
2. **§4.1.**  The paper rules out a constant-coefficient recurrence for `e^{z²}` by Stirling's
   formula applied to `m_{2n} = (2n)!/n!`.  Lean instead uses the exact jets
   `f^{(k)} = H_k(z) e^{z²}` with `deg H_k ≤ k` and `H_k[k] = 2^k`: a constant-coefficient
   equation would make the nonzero polynomial `∑ a_k H_k` (leading coefficient `a_r 2^r`) vanish on
   a neighbourhood.  No asymptotics are needed.
3. **§4.2.**  The paper rules out `D`-finiteness of `tan` by "a solution of a rational-coefficient
   linear ODE has finite singularities".  Lean instead divides the putative equation by
   `tan^{n+1}` and takes the limit at a pole where the leading coefficient is regular
   (`tendsto_eval_div_pow`, `Complex.tendsto_norm_tan_of_cos_eq_zero`), which forces that
   coefficient to vanish.  The same device gives transcendence of `tan` over `ℂ(z)`.

### Scope recorded

Equation (7) is certified in its jet-independence form for **entire** germs, through the corpus
meromorphic jet bridge (`algebraicIndependent_jets_iff`).  The shifted Gamma germ of §4.3 is not
entire, so for it the certified statement is the order form — no algebraic differential equation of
any order — which is exactly clause 3 of Theorem 3.1 for that germ.

## Log

- 2026-08-09 — four process-memory phases separated; \(e^{z^2}\), \(\tan z\), and shifted Gamma fixed
  as strict witnesses; doctrine-relative memory spectrum promoted as CPM's infinite-memory invariant.
- 2026-08-10 — Lean certified in two modules; three paper arguments replaced by compactness,
  leading-coefficient, and pole-limit proofs.
