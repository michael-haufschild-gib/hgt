# Boolean--Sonin full-history and adjoint-mate fracture law

- **ID:** `boolean-sonin-full-history-mate-fracture-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[PROVED HERE] [BRIDGE] [NOT AN RH PROOF]`
- **Scientific status:** `[CORPUS-NEW SYNTHESIS] [PARENT CONTRACTION THEORY]`
  `[CURVATURE COLLIDES WITH EXISTING BURNOL DEFECT-ENERGY LAW]`
- **Parents:**
  - `../new_scientific_knowledge/gamma-copoisson-sonin-independent-quadrant-boundary-transgression.md`;
  - `../new_scientific_knowledge/burnol-sonin-off-axis-aperture-type-rigidity.md`;
  - `burnol-bilateral-aperture-defect-energy-law.md`;
  - `wold-boolean-diagonal-renormalization-mismatch.md`;
  - `../../1-in-progress/riemann-failure-nerve-cobar-antipode-purity-law.md`.
- **Statement:** Two reciprocal contractive Sonin boundary maps canonically generate a normalized
  full binary-history contraction.  On a boundary character its exact history energy is a
  hyperbolic-cosine power, and off the unitary locus one of the two adjoint mates has a
  uniformly nonzero relative defect at every aperture.

## Goal

Construct the finite non-scalar Boolean--Sonin coupling demanded by the Wold--Boolean mismatch,
without identifying the two quadrant clocks and without fitting a norm to a divisor point.
Determine exactly what this coupling proves and what source theorem it still lacks.

## 1. Abstract reciprocal contraction section

Let \(H_j\) be complex Hilbert spaces.  For every \(j\geq0\), let
\[
 T_j^+,T_j^-:H_{j+1}\longrightarrow H_j
 \tag{1}
\]
be contractions.  Fix \(\lambda\in\mathbb C^\times\) and nonzero \(y_j\in H_j\) satisfying
\[
 T_j^+y_{j+1}=\overline\lambda\,y_j,
 \qquad
 T_j^-y_{j+1}=\overline{\lambda^{-1}}\,y_j.
 \tag{2}
\]
The Gamma--co-Poisson--Sonin boundary section satisfies `(1)`--`(2)` with
\(\lambda=r^{\rho-1/2}\).

For a word
\(\omega=(\omega_0,\ldots,\omega_{N-1})\in\{+,-\}^N\), put
\[
 T_\omega
 =
 T_0^{\omega_0}T_1^{\omega_1}\cdots T_{N-1}^{\omega_{N-1}}
 :H_N\longrightarrow H_0.
 \tag{3}
\]
Define the normalized full-history map
\[
 {\cal B}_N:H_N\longrightarrow
 \bigoplus_{\omega\in\{+,-\}^N}H_0,
 \qquad
 ({\cal B}_Nx)_\omega=2^{-N/2}T_\omega x.
 \tag{4}
\]

## 2. Full-history contraction and exact energy

`[PAPER-PROVED] [BOOLEAN_SONIN_FULL_HISTORY_LAW]`

For every \(N\),
\[
 \|{\cal B}_N\|\leq1.
 \tag{5}
\]
Writing \(a=|\lambda|\), the boundary section has exact history energy
\[
 \boxed{\quad
 \|{\cal B}_Ny_N\|^2
 =
 \left(\frac{a^2+a^{-2}}2\right)^N\|y_0\|^2.
 \quad}
 \tag{6}
\]
Consequently
\[
 \|y_N\|
 \geq
 \left(\frac{a^2+a^{-2}}2\right)^{N/2}\|y_0\|.
 \tag{7}
\]

### Proof

For \(x\in H_{j+1}\),
\[
 \frac12\bigl(\|T_j^+x\|^2+\|T_j^-x\|^2\bigr)
 \leq\|x\|^2.
 \tag{8}
\]
Apply `(8)` at every vertex of the binary history tree.  Induction on \(N\) gives
\[
 2^{-N}\sum_{\omega\in\{+,-\}^N}\|T_\omega x\|^2
 \leq\|x\|^2,
 \]
which is `(5)`.

If a word has \(k\) plus signs, `(2)` gives
\[
 T_\omega y_N
 =
 \overline\lambda^{\,k}
 \overline{\lambda^{-1}}^{\,N-k}y_0.
 \tag{9}
\]
There are \(\binom Nk\) such words.  Hence
\[
\begin{aligned}
 \|{\cal B}_Ny_N\|^2
 &=
 2^{-N}\sum_{k=0}^N
 \binom Nk a^{2k}a^{-2(N-k)}\|y_0\|^2\\
 &=
 \left(\frac{a^2+a^{-2}}2\right)^N\|y_0\|^2.
\end{aligned}
\]
This proves `(6)`.  Combine `(5)` and `(6)` to obtain `(7)`.  `QED`

The scalar
\[
 {\cal E}(\lambda)
 :=
 \log\left(\frac{|\lambda|^2+|\lambda|^{-2}}2\right)
 =
 \log\cosh\bigl(2\log|\lambda|\bigr)
 \tag{10}
\]
is the normalized Boolean-history excess energy.  It is nonnegative and vanishes exactly when
\(|\lambda|=1\).

The one-face lower bound in the parent quadrant theorem is asymptotically stronger than `(7)`.
The new content of `(6)` is not a better scalar estimate.  It is the exact coupling of all
\(2^N\) labelled forward/inverse histories before the diagonal quotient identifies words with the
same endpoint.

## 3. Persistent adjoint-mate fracture

Define the two inverse-versus-adjoint defects
\[
\begin{aligned}
 D_j^+
 &:=
 (T_j^+)^*y_j-\overline{\lambda^{-1}}\,y_{j+1},\\
 D_j^-
 &:=
 (T_j^-)^*y_j-\overline\lambda\,y_{j+1}.
\end{aligned}
\tag{11}
\]
The second terms are the algebraic inverse lifts dictated by `(2)`.  The first terms are the
physical Hilbert adjoint lifts.  Thus `(11)` is the literal finite-aperture mate defect, not a
dagger imposed on a specialized scalar character.

Use the convention that the Hilbert inner product is linear in the first variable.  Let
\(P_{j+1}\) be orthogonal projection onto \(\mathbb C y_{j+1}\), and define the radial mate
coefficients \(d_j^\pm\in\mathbb C\) by
\[
 P_{j+1}D_j^\pm=d_j^\pm y_{j+1}.
\tag{12}
\]
Put
\[
 R_j=\frac{\|y_{j+1}\|}{\|y_j\|}.
\tag{13}
\]
Taking the inner product of `(11)` with \(y_{j+1}\) and using `(2)` gives
\[
\begin{aligned}
 d_j^+
 &=\frac{\lambda}{R_j^2}-\overline{\lambda^{-1}},\\
 d_j^-
 &=\frac{\lambda^{-1}}{R_j^2}-\overline\lambda.
\end{aligned}
\tag{14}
\]
Consequently the aperture norm cancels from the normalized difference:
\[
 \boxed{\quad
 \lambda^{-1}d_j^+-\lambda d_j^-
 =
 |\lambda|^2-|\lambda|^{-2}.
 \quad}
\tag{15}
\]

`[PAPER-PROVED] [RECIPROCAL_CONTRACTION_ADJOINT_MATE_FRACTURE]`

For every \(j\),
\[
 \boxed{\quad
 \max\{\|P_{j+1}D_j^+\|,\|P_{j+1}D_j^-\|\}
 \geq
 \left||\lambda|^2-|\lambda|^{-2}\right|\|y_j\|.
 \quad}
\tag{16}
\]
In particular, if both relative mate defects tend to zero along any cofinal sequence,
\[
 \frac{\|D_j^+\|}{\|y_j\|}\longrightarrow0,
 \qquad
 \frac{\|D_j^-\|}{\|y_j\|}\longrightarrow0,
\tag{17}
\]
then \(|\lambda|=1\).

### Proof

The adjoint identity and `(2)` give
\[
\begin{aligned}
 \left\langle (T_j^+)^*y_j,y_{j+1}\right\rangle
 &=\lambda\|y_j\|^2,\\
 \left\langle (T_j^-)^*y_j,y_{j+1}\right\rangle
 &=\lambda^{-1}\|y_j\|^2.
\end{aligned}
\tag{18}
\]
Division by \(\|y_{j+1}\|^2\) and subtraction of the inverse-lift coefficients prove `(14)`.
Multiplying its first formula by \(\lambda^{-1}\), its second by \(\lambda\), and subtracting
proves `(15)`.

Now suppose that \(a=|\lambda|\geq1\).  The first equation in `(2)` and contractivity give
\[
 R_j\geq a.
 \tag{19}
\]
By `(14)`,
\[
\begin{aligned}
 \frac{\|P_{j+1}D_j^-\|}{\|y_j\|}
 &=R_j\left|\frac{a^{-1}}{R_j^2}-a\right|\\
 &=aR_j-\frac{a^{-1}}{R_j}\\
 &\geq a^2-a^{-2}.
\end{aligned}
\tag{20}
\]
If \(a\leq1\), use the second equation in `(2)` to get
\(R_j\geq a^{-1}\), and apply the same argument to \(D_j^+\):
\[
 \frac{\|P_{j+1}D_j^+\|}{\|y_j\|}
 \geq a^{-2}-a^2.
\tag{21}
\]
Equations `(20)`--`(21)` prove `(16)`.  Equation `(17)` then forces
\(a^2-a^{-2}=0\), hence \(a=1\).  `QED`

Formula `(15)` is stronger conceptually than the norm estimate.  Orthogonal aperture leakage and
the unknown kernel-norm growth \(R_j\) may affect the two mates separately, but neither affects
their signed radial curvature.

The later Burnol aperture-type theorem gives
\[
 \lim_{j\to\infty}\frac1j\log R_0R_1\cdots R_{j-1}
 =
 |\log|\lambda||.
\tag{21a}
\]
Thus an off-line fibre has exactly the least exponential growth allowed by the dominant one-sided
Wold character.  For \(|\lambda|>1\), the plus direction accounts for that growth while `(16)`
forces a persistent minus radial fracture; for \(|\lambda|<1\), the roles reverse.  This does not
assert convergence of the individual one-step norm ratios.
Functional-equation reflection swaps the two failures but does not cancel their unsigned
full-history energy.

The theorem distinguishes two statements often conflated in the corpus:

```text
two downward maps are contractions:
  already proved; allows exponentially growing inverse-system lifts;

generated inverse equals Hilbert adjoint in both orientations:
  fails by a fixed relative amount at every level whenever the character is off-unitary.
```

## 4. Literal Riemann boundary specialization

For the Gamma--co-Poisson--Sonin section,
\[
 \lambda=\lambda_r(\rho)=r^{\rho-1/2},
 \qquad
 |\lambda|=r^{\Re\rho-1/2}.
 \tag{22a}
\]
The full-history excess is therefore
\[
 {\cal E}_r(\rho)
 =
 \log\cosh\left(2(\Re\rho-\tfrac12)\log r\right).
 \tag{22b}
\]
If \(Q_\rho=m_\rho(\tfrac12-\Re\rho)\) is the already verified
Julia/shell/Sonin modular charge, then
\[
 {\cal E}_r(\rho)
 =
 \log\cosh\left(\frac{2Q_\rho}{m_\rho}\log r\right).
 \tag{22c}
\]
Thus the signed local charge and the nonnegative full-history energy are respectively the first
orientation and the Boolean-history convexification of the same character.

Equation `(16)` becomes
\[
 \max\{\|P_{j+1}D_j^+(\rho)\|,\|P_{j+1}D_j^-(\rho)\|\}
 \geq
 2\left|\sinh\left(2(\Re\rho-\tfrac12)\log r\right)\right|
 \|y_{\rho,j}\|.
 \tag{22d}
\]
Every off-line zero therefore produces a persistent, macroscopic failure of one literal
Gamma--co-Poisson adjoint mate at every aperture.  It is not a defect visible only after a
delicate cofinal limit.

More exactly, the two radial coefficients satisfy
\[
 \lambda_r(\rho)^{-1}d_j^+(\rho)
 -
 \lambda_r(\rho)d_j^-(\rho)
 =
 2\sinh\left(2(\Re\rho-\tfrac12)\log r\right).
\tag{22e}
\]
The right side is independent of \(j\).  It is the signed, unsquared radial mate curvature of the
same modular charge measured by `(22c)`.

## 5. What this changes

The Wold--Boolean mismatch left the finite coupled carrier unspecified.  Equations `(4)`--`(6)`
construct it canonically from the two already source-defined Sonin contractions:

```text
Boolean channel:
  retains every labelled forward/inverse history and supplies the factor 2^N;

Sonin/Wold channel:
  supplies the reciprocal character weights lambda and lambda^(-1);

coupled full-history law:
  normalized energy = cosh(2 log|lambda|)^N;

diagonal quotient:
  forgets word order and can cancel radial drift;

adjoint-mate defect:
  records exactly why a reciprocal inverse-system section need not be a dagger section.
```

This does not prove the source mate is radially balanced.  It removes a weaker ambiguity:
the missing theorem is not construction of a finite Boolean--Wold coupling and not another
one-sided contraction.  It is the same-fibre radial mate identity for the explicit coefficients
in `(22e)`, derived from the source before specialization.

### Corpus collision: the curvature was already present

The scalar in `(15)` and `(22e)` is not a new Riemann orientation law.  The existing
`burnol-bilateral-aperture-defect-energy-law.md` proves, for the literal ambient Sonin leakage
vectors,
\[
 \|\epsilon^-_{a,r,w}\|^2-\|\epsilon^+_{a,r,w}\|^2
 =
 \left(|\lambda_r(w)|^2-|\lambda_r(w)|^{-2}\right)
 \|Z_w^a\|^2.
\tag{24}
\]
Thus `(15)` is the radial adjoint-mate/projection representation of the already-proved Burnol
bilateral defect-energy curvature `(24)`.  The Boolean full-history object remains a useful
explicit coupling, but its binomial/Fock algebra is parent contraction theory and its scalar
growth bound is weaker than the one-face Sonin bound.

This collision fixes the honest frontier.  The same-fibre balance condition was already known.
Neither the Boolean history nor the adjoint-mate coordinates supply its source producer.

The new all-orders-flat theorem sharpens the type of any possible producer.  On the actual Wold
boundary, one reflected sector is flat beyond every finite Rees order and the vacuum
half-density sector is not.  Hence no finite-Rees reporter family, in any dimension, can realize
the required source transpose.  Arbitrary essential growth is also insufficient:
`source-linear-essential-superselection-no-sewing.md` proves that every closed source-linear
relation between the off-line reflected prime sectors splits.  Therefore a viable transpose must
be constructed **before ordinary boundary closure**, as a source-normal exponential associated
grade or relative Bockstein measuring the noncommutation of source-normal specialization with
closure.  Calling an after-closure defect balance a transpose merely restates the endpoint.

## 6. RH-equivalent source producer target: mate curvature is boundary-ideal exact

The universal reinterpretation suggested by the literal formulas is:

> **The co-Poisson boundary carries the entire mismatch between arithmetic reversal and analytic
> adjunction.  When the boundary ideal vanishes, no radial mismatch can remain.**

This changes the role of a zero.  A zero is not first a spectral value.  It is a point where the
source compensation term disappears.  An off-line zero could survive only if a nonzero mate
curvature remained after its unique source carrier had vanished.

For regular \(w\) with nonzero quotient evaluators, define \(D_j^\pm(w)\) by `(11)` with
\(\lambda=\lambda_r(w)\), and put
\[
\begin{aligned}
 {\mathfrak K}_j(w)
 &:=
 \lambda_r(w)^{-1}
 \left\langle D_j^+(w),y_{w,j+1}\right\rangle\\
 &\phantom{:=}\;
 -
 \lambda_r(w)
 \left\langle D_j^-(w),y_{w,j+1}\right\rangle.
\end{aligned}
\tag{25}
\]
Let \(\Lambda_j(w)\) be the completed co-Poisson multiplier from `(GS9)`.

`[BOLD CONJECTURE] [COPOISSON_MATE_CURVATURE_IDEAL_EXACTNESS]`

> Before divisor specialization, the literal Gamma/co-Poisson source transpose constructs
> locally bounded source reporters \(A_j,B_j,C_j,E_j\), extending across every nontrivial Xi
> divisor point, such that
> \[
> \begin{aligned}
> {\mathfrak K}_j(w)
> &=
> \Lambda_j(w)A_j(w)
> +\Lambda_{j+1}(w)B_j(w)\\
> &\quad+
> \overline{\Lambda_j(w)}C_j(w)
> +\overline{\Lambda_{j+1}(w)}E_j(w).
> \end{aligned}
> \tag{26}
> \]
> The reporters are generated by the off-divisor co-Poisson ideal and the two aperture
> projections; none is defined by division by \(\Lambda_j\), by a zero, or by a fitted norm.
> Their joint construction is the boundary value of a source-normal exponential Bockstein formed
> before ordinary Hilbert closure; it is not a finite-Rees operator or an after-closure relation.

The statement is frozen as a truth-hunch.  The already-proved down-map errors `(GS10)` are
co-Poisson-ideal multiples, and the full-history law shows that no additional finite Boolean
record is missing.  What is unknown is whether the independently constructed source transpose
places the radial adjoint errors in the same ideal.

### First attack: the existing quotient maps leave exactly the curvature class

`[PAPER-PROVED] [COPOISSON_MATE_CURVATURE_QUOTIENT_CLASS]`

Write the two errors in `(GS10)` as
\[
\begin{aligned}
 e_j^+(w)&=E_jU_r^*c_{w,j+1},\\
 e_j^-(w)&=E_jU_rc_{w,j+1}.
\end{aligned}
\tag{27}
\]
With the linear-in-first convention, direct substitution of `(GS10)` into `(25)` gives
\[
\boxed{\quad
 {\mathfrak K}_j(w)
 =
 \left(
 |\lambda_r(w)|^2-|\lambda_r(w)|^{-2}
 \right)\|y_{w,j+1}\|^2
 +
 \Lambda_{j+1}(w){\mathfrak R}_j(w),
\quad}
\tag{28}
\]
where
\[
 {\mathfrak R}_j(w)
 =
 \lambda_r(w)\langle y_{w,j},e_j^-(w)\rangle
 -
 \lambda_r(w)^{-1}\langle y_{w,j},e_j^+(w)\rangle.
\tag{29}
\]

Indeed,
\[
\begin{aligned}
\langle D_j^+(w),y_{w,j+1}\rangle
 &=
 \lambda\|y_{w,j}\|^2
 -
 \Lambda_{j+1}(w)\langle y_{w,j},e_j^+(w)\rangle\\
 &\quad-
 \overline{\lambda^{-1}}\|y_{w,j+1}\|^2,\\
\langle D_j^-(w),y_{w,j+1}\rangle
 &=
 \lambda^{-1}\|y_{w,j}\|^2
 -
 \Lambda_{j+1}(w)\langle y_{w,j},e_j^-(w)\rangle\\
 &\quad-
 \overline\lambda\|y_{w,j+1}\|^2.
\end{aligned}
\tag{30}
\]
Multiply by \(\lambda^{-1}\) and \(\lambda\), respectively, and subtract.  The
\(\|y_{w,j}\|^2\) terms cancel, the two target terms give the displayed character curvature, and
the errors give `(29)`.  This proves `(28)`.  `QED`

Therefore the class of \({\mathfrak K}_j\) modulo the existing co-Poisson boundary ideal is
already exactly
\[
 \left[
 \left(|\lambda|^2-|\lambda|^{-2}\right)\|y_{w,j+1}\|^2
 \right].
\tag{31}
\]
No further manipulation of `(GS10)`, no sharper Sonine norm estimate, and no finite-history
identity can prove `(26)`.  The conjecture requires an independently constructed source transpose
whose comparison supplies a new relation killing `(31)`.  Without that second construction,
`(26)` is merely the RH-bearing demand that the known quotient class vanish.

At a nontrivial zero \(\rho\), all four ideal generators in `(26)` vanish, while
\(y_{\rho,j+1}\ne0\).  Equations `(15)` and `(25)` give
\[
 {\mathfrak K}_j(\rho)
 =
 \left(
 |\lambda_r(\rho)|^2-|\lambda_r(\rho)|^{-2}
 \right)\|y_{\rho,j+1}\|^2.
 \tag{32}
\]
Thus `(26)` would force \(|\lambda_r(\rho)|=1\), hence
\(\Re\rho=\tfrac12\).  Proving the source-generated, nondivisive factorization `(26)` would
therefore complete an unconditional RH proof.

### Conjecture falsifiers

1. The source transpose produces a mate-curvature term whose class modulo the real co-Poisson
   ideal is nonzero.
2. A coefficient in `(26)` necessarily has a pole at an annihilator character; writing
   \({\mathfrak K}/\Lambda\) off the divisor is tautological and does not count.
3. The factorization exists only after inserting the Xi divisor, a zero-dependent metric, or the
   equality \(|\lambda|=1\).
4. A generalized-prime off-line system carries the same literal ordinary-integer
   Gamma/co-Poisson source transpose and satisfies `(26)`.
5. The two aperture adjoints require an extra boundary object not generated by the co-Poisson
   ideal.  That object, rather than `(26)`, is then the positive survivor to classify.

The first algebraic attack realizes item 5 in a precise form: the extra quotient class is `(31)`.
It does not falsify the conjectured independent source-transpose comparison, but it closes every
attempt to derive that comparison from the already-known down-map factorization alone.

## 7. RH-bearing open core

`[OPEN CORE] [SOURCE_GLOBAL_RADIAL_ADJOINT_MATE_CONTROL]`

Construct the Gamma/co-Poisson reporter mate off the divisor on the full filtered
Boolean--Sonin history object as a source-normal exponential Bockstein **before ordinary
closure**.  Prove from the literal ordinary-prime source, with no zero-dependent normalization,
that its Gamma/co-Poisson/Sonin boundary is the ideal factorization `(26)`.  Its annihilator
specialization is the same-fibre radial mate identity
\[
 \lambda_r(\rho)^{-1}d_j^+(\rho)
 =
 \lambda_r(\rho)d_j^-(\rho).
\tag{33}
\]
By `(22e)`, this would force \(\Re\rho=\tfrac12\) for every nontrivial Xi zero.

Raw defect vanishing is deliberately not conjectured: changing Sonin aperture can create
tangential projection leakage even for a unitary character.  Projection to the conormal line and
the difference `(22e)` already remove both that leakage and the unknown aperture norm.  What
remains is to prove `(26)` from the off-divisor source mate rather than impose `(33)` on a zero.

## 8. Hostile audit

1. **Not a stronger norm lower bound.**  The parent one-face estimate
   \(\|y_N\|\geq\max(a^N,a^{-N})\|y_0\|\) dominates `(7)`.  The survivor is the labelled
   full-history coupling and mate defect, not scalar growth.
2. **No RH from two contractions.**  An inverse tower of contractions can pay arbitrary
   exponential lift growth.  Equations `(5)`--`(7)` do not imply \(|\lambda|=1\).
3. **Sharp Sonin growth closes the norm attack.**  The companion Burnol theorem proves that
   off-axis evaluator growth already has the exact exponent \(|\log|\lambda||\).  Improving an
   ambient Cauchy--Schwarz estimate cannot prove the missing mate identity.
4. **No raw-mate overclaim.**  The Hilbert adjoint need not reproduce the inverse lift even on
   the critical line because the aperture projections may leak in zero-rate directions.
5. **No diagonal cancellation.**  The \(2^N\) history labels are retained.  Passing only to the
   endpoint count \(k\) or to \(p=q\) discards the record this theorem constructs.
6. **No zero-fitted completion.**  The maps and the \(2^{-N/2}\) Boolean normalization are fixed
   before \(\lambda\).  Normalizing each local vector by its \(\lambda\)-dependent norm would be
   external modular retuning.
7. **Generalized-prime falsifier survives.**  An off-line Euler system realizes
   \({\cal E}(\lambda)>0\) and a nonzero mate defect.  The theorem detects that failure; it does
   not exclude it.
8. **Parent-theory boundary.**  Iterated column contractions, defect operators, and binomial
   character energies are standard multivariable contraction/Fock-space algebra.  No novelty is
   claimed for the abstract inequalities.
9. **Exact remaining novelty target.**  Any candidate-new content begins only with an
   ordinary-prime Gamma/co-Poisson theorem constructing the pre-closure exponential Bockstein and
   proving that its Sonin boundary is the nondivisive ideal factorization `(26)` before divisor
   specialization.

## Literature boundary

Contractive tuples, their defect operators, and full-Fock dilations are established operator
theory.  A targeted search found no source-specific result coupling Burnol's co-Poisson quotient
evaluation kernels to the complete labelled reciprocal-dilation history or identifying the
resulting adjoint-mate fracture with the Riemann modular charge.  This is provisional
noncollision evidence for the synthesis only, not for the abstract theorem.

## Lean decision

The abstract estimates are elementary and would formalize without the Burnol spaces.  Such a
wrapper would not formalize the literal boundary comparison or the radial mate defect and would
therefore be theatre.  Lean work is deferred until the co-Poisson evaluation/projection
interfaces exist.

## Gates

- [x] 0 → 1: full-history object and mate defect specified
- [x] 1 → 2: contraction, energy, and fracture estimates proved on paper
- [x] corpus collision and parent-theory audit
- [ ] construct off-divisor filtered reporter mate
- [x] remove aperture-norm growth and orthogonal leakage from radial curvature
- [x] identify curvature with the existing Burnol bilateral defect-energy law
- [x] exclude finite-Rees and after-closure source-linear reporters
- [ ] prove co-Poisson mate-curvature ideal exactness `(26)`
- [ ] add Burnol analytic interfaces to Lean

## Log

- 2026-07-31 — Constructed normalized full binary-history contraction from the two literal Sonin
  quotient maps.  Proved exact hyperbolic-cosine history energy and persistent off-unitary
  adjoint-mate fracture.  Replaced vague “couple Boolean and Wold channels” with an explicit finite
  object and isolated radial mate control as the remaining RH-bearing theorem.
