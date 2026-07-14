# Prime--archimedean Bernstein purity divergence law

- **ID:** `prime-arch-bernstein-purity-divergence-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[FORMAL STRENGTHENING; NOVELTY UNCLAIMED]`
- **Statement:** The endpoint Bernstein purity is uniformly mass-bounded under RH and tends to
  positive infinity under failure of RH. Consequently RH is equivalent to one fixed purity bound
  recurring at arbitrarily large degrees, and this cofinal condition is equivalent to the
  prime--polar critical absolute-abscissa bound.

## Main law `[PROVED HERE]`

Let

\[
 \Pi_n=
 \sum_{j=0}^{n}
 \left(\Delta^{n-j}
   \left(\frac{m_j}{R^j}\right)\right)^2
\]

be the source-defined endpoint Bernstein purity, with the established prime--Gamma moment source
and endpoint Hausdorff radius. Then exactly one of the following alternatives holds:

\[
 \mathrm{RH}
 \quad\Longrightarrow\quad
 \Pi_n\le m_0^2\quad(n\ge0),
\]

or

\[
 \neg\mathrm{RH}
 \quad\Longrightarrow\quad
 \Pi_n\longrightarrow+\infty.
\]

More quantitatively, failure of RH supplies constants \(\rho>1\) and \(\eta>0\) such that

\[
 \eta\rho^n\le(n+1)\Pi_n
\]

for every sufficiently large \(n\).

Define cofinal boundedness by

\[
 \exists C\in\mathbb R\;\forall N\;\exists n\ge N,
 \qquad \Pi_n\le C.
\]

Then

\[
 \mathrm{RH}
 \iff
 \Pi_n\text{ is cofinally bounded}
 \iff
 \Pi_n\not\longrightarrow+\infty.
\]

Thus uniform control, convergence, monotonicity, and a bound at every degree are unnecessary. One
bounded cofinal sampling of the positive scalar is sufficient.

## Proof

Write

\[
 u_q=\frac{\lambda_q}{R},
 \qquad
 B(q)=|u_q|+|1-u_q|,
\]

where \(\lambda_q\) is the multiplicity-exact central reciprocal-square coordinate. Absolute
summability of \((\lambda_q)_q\) implies \(u_q\to0\) off finite sets, hence \(B(q)\to1\) off finite
sets.

If RH fails, one coordinate \(u_{q_0}\) is nonreal. The strict focal-ellipse inequality gives

\[
 B(q_0)=|u_{q_0}|+|1-u_{q_0}|>1.
\]

Therefore \(B\) has a global maximum \(r>1\), attained on a nonempty finite packet. Choose a
maximizer \(q_*\) and the alignment phase

\[
 w=\frac{\overline{u_{q_*}}}{|u_{q_*}|}
    \frac{1-u_{q_*}}{|1-u_{q_*}|},
 \qquad |w|=1.
\]

For the affine modes

\[
 b_q=1-u_q+u_qw
\]

one has \(|b_q|\le B(q)\le r\), while \(|b_{q_*}|=r\). Let \(F\) be the finite packet on which
\(|b_q|=r\). Equality throughout the two triangle inequalities forces every \(q\in F\) to have
the same alignment phase and the same elliptic radius as \(q_*\).

The ellipse-rigidity lemma proves that these two values determine a nonreal coordinate up to

\[
 u_q=u_{q_*}
 \quad\text{or}\quad
 u_q=1-\overline{u_{q_*}}.
\]

Every off-line endpoint coordinate lies in the strict disk \(|u|<1/4\). The second alternative is
therefore impossible: if it held, the triangle inequality would give

\[
 1\le |u_q|+|u_{q_*}|<\frac12.
\]

Hence all maximal affine modes have the same coordinate, the same mode \(b_{q_*}\), and the same
nonzero coefficient \(\lambda_{q_*}\). Their aggregate coefficient is a positive multiplicity
times \(\lambda_{q_*}\), so it is nonzero.

After division by \(r^n\), every mode outside \(F\) lies strictly inside the unit disk. Dominated
convergence kills that summable tail. The maximal packet is one common rotating unit mode with a
nonzero aggregate coefficient. Consequently there is \(\delta>0\) such that, eventually,

\[
 \left|
   \frac{\mathcal B_n(w)}{r^n}
 \right|\ge\delta,
\]

where \(\mathcal B_n(w)\) is the complete source Bernstein pencil.

The unit-circle transform bound and finite-dimensional Cauchy--Schwarz give

\[
 |\mathcal B_n(w)|^2
 \le \|c^{(n)}\|_1^2
 \le(n+1)\Pi_n.
\]

Thus, eventually,

\[
 \delta^2(r^2)^n\le(n+1)\Pi_n.
\]

Since a positive exponential divided by \(n+1\) tends to positive infinity, so does \(\Pi_n\).
The RH branch uses the already formalized sharp estimate \(\Pi_n\le m_0^2\). The cofinal criterion
follows immediately: a sequence tending to positive infinity cannot return below one fixed bound
arbitrarily far out.

## Direct RH-source consequence

For every admissible rectangle \((L,N)\), Lean proves

\[
 \Pi_n\text{ is cofinally bounded}
 \iff
 \sigma_{\mathrm{abs}}
 \left(
   \sum_{n\ge1}
   S^-_{L,N}(n)n^{-s}
 \right)\le1.
\]

This does not establish the right-hand side unconditionally. It replaces that remaining
absolute-abscissa obligation by the positive scalar task of finding one fixed purity ceiling at
arbitrarily large degrees.

## Lean certificate

Formal files:

- `formal/GaloisForLFunctions/RHTower/BernsteinEllipseRigidity.lean`
- `formal/GaloisForLFunctions/RHTower/FiniteExponentialPencilDominantConstant.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinPurityDivergence.lean`

Principal declarations:

- `eq_or_eq_one_sub_conj_of_bernsteinEllipsePhase_eq_of_amplitude_eq`
- `eventually_norm_tsum_normalizedExponentialPencil_ge_of_dominant_constant`
- `exists_unit_xiCentralBernsteinPencil_eventually_exponential_of_not_riemannHypothesis`
- `exists_eventually_exponential_lower_envelope_primeArchEndpointBernsteinPurity_of_not_rh`
- `tendsto_primeArchEndpointBernsteinPurity_atTop_of_not_riemannHypothesis`
- `riemannHypothesis_iff_primeArchEndpointBernsteinPurity_cofinallyBounded`
- `primeArchEndpointBernsteinPurityCofinallyBounded_iff_rectangularPrimePolarSource_negativeAbscissa_le_one`
- `primeArchEndpointBernsteinPurity_dichotomy`

Verification:

- all three new modules compile individually with the repository toolchain;
- `scripts/formal_tools.py lint` passes without a build;
- the declarations use only Lean/mathlib's standard logical axioms `propext`,
  `Classical.choice`, and `Quot.sound`;
- there is no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration in the proof
  surface;
- no full project build was run.

## Exact open core

Construct, from the prime--Gamma source or a source-faithful operator/thermal realization, a fixed
constant \(C\) and arbitrarily large degrees \(n\) satisfying

\[
 \Pi_n\le C.
\]

That positive cofinal recurrence now closes the prime--polar absolute-abscissa target and RH
directly.
