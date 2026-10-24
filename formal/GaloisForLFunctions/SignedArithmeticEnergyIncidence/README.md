# Signed Arithmetic Energy and Incidence

Signed Arithmetic Energy and Incidence studies **which operations preserve a
source's signed energy**. Its four recurring tasks are local payment,
completion in a new norm, transport in a parameter and analysis of adverse
sequences. It supplies interface theorems for the other programmes rather
than introducing another critical form.

The central issue is that positive pieces need not assemble into a positive
whole, and a source controlled in one topology may escape the receiver norm.
The programme identifies exact conditions for those transfers, then asks
whether the arithmetic source satisfies them uniformly.

## Signed forms and local payment

For a finite symmetric coupling $C=(c_{ij})$, write
$E_C(f)=\sum_{i,j}c_{ij}f_if_j$. Diagonal entries are budgets and off-diagonal
entries are overlap charges. A **local allocation** consists of shares
$a_{ij}\ge0$ such that

$$
c_{ij}^2\le a_{ij}a_{ji},\qquad
\sum_{j\ne i}a_{ij}\le c_{ii}.
$$

These inequalities pay every pair without spending a diagonal budget twice.
They are sufficient for positivity, but not necessary for every signed form.

**Switching** replaces $c_{ij}$ by $s_is_jc_{ij}$, $s_i\in\{\pm1\}$.
A pattern is **balanced** if switching makes all overlaps nonpositive. Products
of the edge signs $-\operatorname{sgn}(c_{ij})$ around cycles detect the
obstruction; a nontrivial product is **frustration**.

The foundational classification concerns the entire sign pattern: local
payment is lossless for every positive form realizing that pattern exactly
when its cycles are aligned. Frustrated patterns can require a global square
that no independent pair allocation captures. This is why taking absolute
values before allocation changes the problem.

The signed ground-state identity is another useful bridge:

$$
E_C(vg)=\sum_i v_i(Cv)_i g_i^2
 -\frac12\sum_{i,j}c_{ij}v_iv_j(g_i-g_j)^2.
$$

A supersolution pays the form only when the remainder has the required sign.
The identity alone grants neither balance nor positivity.

## Arithmetic sources and their topology

The main infinite example is the centred Möbius damping chain. Its orbit of
the reciprocal vector $1/k$ is the normalized divisor-prefix receiver.
Admission is membership of this particular orbit in $\ell^2$.

The residue mode

$$
v_d(n)=\frac{\lfloor(n+1)/d\rfloor}{n+1}-\frac1d
$$

has norm of order $d^{-1/2}$. The absolute sum of the damped mode norms
therefore converges only above half damping. The actual signed source reaches
the endpoint by cancellation, while the all-positive coefficient envelope
does not. This identifies a boundary of the triangle-inequality method.

The centred chain is Hilbert–Schmidt above half damping, compact at half
damping and continuous there in operator norm from above. It has no uniform
backward stability estimate. Boundedness below half damping is stronger than
admission of the one source orbit: it controls all combinations of columns and
their mixed terms. An endpoint compactness theorem does not provide that
continuation.

## Sampling and adverse sequences

**Companion payment** asks whether positive sample values can dominate an
adverse derivative term. Finite polynomial interpolation gives an exact
Lagrange price. Paley–Wiener kernel Grams give the corresponding genuine
band-limited problem, with approximation errors required when moving between
the two settings.

One sharp model removes a single sample from a Nyquist lattice. A positive
derivative mass can still be paid exactly at heights where the derivative of
the missing sample's sinc kernel vanishes; elsewhere that sinc supplies a
counterexample. Constructing suitable companions from the actual zero divisor
is a separate arithmetic task.

**Compact negativity** localizes adverse directions at each fixed aperture to
finite-rank charges plus a small norm error. It does not make an increasing
family collectively compact. A useful global decomposition must retain the
source normalization, pole functional and mass that moves with the aperture.

## Research questions

- Which global allocation pays the frustrated arithmetic form with one shared
  reserve and controlled overlap as the carrier grows?
- Which source-specific cancellation controls the Möbius orbit below half
  damping, without demanding unnecessary bounds on the entire operator?
- Can actual zero geometry supply companion sampling with controlled local
  approximation error and infinite tail, yielding an unrestricted $L^2$ floor?
- Can adverse profiles be localized uniformly across aperture in a topology
  that retains the signed receiver?

The existing all-parity Sobolev floor in
[Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) leaves
the plain-$L^2$ sampling problem open. Finite Gram positivity and separate
compactness at each aperture likewise leave their growing-family transfer open.

## Place in the wider research

[Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md)
supplies the crossing strips and prime-tower charges.
[Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) supplies
residue modes and the damping chain.
[Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md)
supplies the signed transport budget.
[Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md) retains
cofactor work and normalized mass when fixed observations disappear.

Start with the transfer being proposed—allocation, completion or continuation—
and its exact norm. The [programme umbrella](../SignedArithmeticEnergyIncidence.lean)
maps the finite and Hilbert-space tools.
