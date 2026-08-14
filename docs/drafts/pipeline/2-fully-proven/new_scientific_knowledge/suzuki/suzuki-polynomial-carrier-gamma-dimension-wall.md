# Polynomial orbit carriers meet a sharp Gamma dimension wall

- **ID:** `suzuki-polynomial-carrier-gamma-dimension-wall`
- **Stage:** 2 — fully proved on paper
- **Type:** SHARP HARDY-ARCHITECTURE CLASSIFICATION / POSITIVE RANK-ONE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-log-recurrence-polynomial-carrier-trichotomy.md`,
  `suzuki-gamma-wall-block-hardy-and-derivative-scattering.md`,
  `suzuki-literal-paired-source-assembly.md`

## 1. Result

The previous polynomial-carrier theorem proved a polynomial two-sided prime-group bound and then
treated that bound as sufficient for Gamma Hardy transfer. It is not sufficient without comparing
its degree to the exact Gamma decay.

Let the visible-prime valuation rank be (d), use the radial polynomial weight

\[
 w_\kappa(\nu)=\langle\nu\rangle^{-\kappa},\qquad
 \langle\nu\rangle=1+|\nu|_1,
\]

and let (0<\sigma<1) be a vertical Gamma shift. The two exact requirements for a uniform
all-vector direct Hardy theorem are

\[
 \kappa>\frac d2                                             \tag{1}
\]

for a bounded physical orbit state to lie in the weighted lattice Hilbert space, and

\[
 \kappa<\sigma                                               \tag{2}
\]

for the polynomially distorted homogeneous Gamma carrier to remain in (L^2) on the shifted
frequency line. Since (\sigma<1), a common exponent exists exactly when

\[
 d\le1.                                                       \tag{3}
\]

Thus:

```text
rank d = 0 or 1:
  a radial polynomial carrier has a genuine Gamma-Hardy window;

rank d >= 2:
  no radial polynomial exponent can simultaneously embed every bounded orbit state
  and make the worst-case homogeneous Gamma transport square integrable.          (4)
```

This is a classification of the **uniform radial polynomial-carrier proof architecture**. It
does not exclude a source-selected vector whose prime orbit grows more slowly than the operator
norm, nor a reciprocal biweighted Evans cancellation. Those are precisely the survivors.

## 2. Exact Gamma threshold

The squared scalar trace-zero Gamma carrier on (z=x+i\sigma) is

\[
 q_\sigma(x)=
 \frac{|\Gamma(1-\sigma+ix)|}{|\Gamma(1+\sigma+ix)|}
 \frac1{|x+i\sigma|}.                                    \tag{5}
\]

The already-proved vertical Gamma-ratio asymptotic gives

\[
 q_\sigma(x)|x|^{1+2\sigma}\longrightarrow1
 \quad (|x|\to\infty).                                  \tag{6}
\]

A degree-(\kappa) polynomial group estimate costs at worst (\langle x\rangle^\kappa) in
norm, hence (langle x\rangle^{2\kappa}) in squared norm. Put

\[
 q_{\kappa,\sigma}(x)=|x|^{2\kappa}q_\sigma(x).          \tag{7}
\]

Then exactly

\[
 q_{\kappa,\sigma}(x)|x|^{1+2\sigma-2\kappa}
 \longrightarrow1.                                     \tag{8}
\]

The power-integral criterion therefore gives

\[
 q_{\kappa,\sigma}\in L^1(\mathbb R)
 \quad\Longleftrightarrow\quad
 -1-2\sigma+2\kappa<-1
 \quad\Longleftrightarrow\quad
 \kappa<\sigma.                                        \tag{9}
\]

This is sharp, including the logarithmically divergent boundary (\kappa=\sigma).

## 3. Exact lattice threshold

For bounded coordinate samples, the squared carrier norm is controlled by

\[
 \sum_{\nu\in\mathbb Z^d}\langle\nu\rangle^{-2\kappa}.
                                                               \tag{10}
\]

The shell (|\nu|_1=N) has order (N^{d-1}) points, so `(10)` has the same convergence threshold
as

\[
 \sum_{N\ge1}N^{d-1-2\kappa}.
\]

Consequently `(10)` converges exactly when `(1)` holds. Combining `(1)`, `(2)`, and
(\sigma<1) gives

\[
 \frac d2<\kappa<\sigma<1.                              \tag{11}
\]

If (d\ge2), then (d/2\ge1), contradicting `(11)`. If (d\le1), the concrete choice

\[
 \kappa=\frac23,\qquad \sigma=\frac34                  \tag{12}
\]

works. For (d=1), its lattice square is the convergent series

\[
 \sum_{n\in\mathbb Z}(1+|n|)^{-4/3}.                   \tag{13}
\]

This proves `(3)`.

## 4. Correction to the prior Hardy claim

The paired Gamma--logistic card assumed only

```text
||exp(-ixB/2)|| + ||exp(ixB/2)|| <= C(1+|x|)^m.
```

Its homogeneous factor is the scalar Gamma carrier times (\exp(-ixB/2)). The displayed bound
only yields squared density

\[
 O(|x|^{-1-2\sigma+2m}),                                \tag{14}
\]

which is integrable only for (m<\sigma). An arbitrary polynomial degree is not enough. Rough
block forcing cannot repair a nonintegrable homogeneous component; that would require a
source-selected stable/unstable cancellation.

The corrected direct theorem is therefore:

```text
uniform group growth degree κ < σ
+ Gamma block source
+ zero regular-singular charges
 -> shifted value L2.                                   (15)
```

Alternatively one may replace the uniform degree condition by a vectorwise bound on the actual
homogeneous coefficient. The latter is an Evans/dichotomy statement, not a consequence of
boundedness or polynomial group growth alone.

## 5. Rank-one positive survivor

For one visible prime, opposite-end and zero event times are uniformly bounded outside finitely
many labels: (\ell(n)=n\log p) leaves every bounded physical window as (|n|\to\infty).
Hence no positive logarithmic recurrence exponent is spent. The window `(12)` simultaneously
provides:

1. a square-summable carrier for every bounded orbit sample;
2. polynomial group growth strictly below the Gamma shift;
3. a square-integrable homogeneous Gamma majorant;
4. the literal source block summability supplied by paired source assembly.

What remains before declaring the one-prime trace-zero (H^1_0) theorem is the source-faithful
rough primitive one-block transfer and the finite-cell compact-middle elliptic argument. The
dimension obstruction is absent there; those are now concrete analytic lemmas rather than an
unspecified finite-to-flat expansion.

## 6. Rank-two-and-higher survivor

For (d\ge2), increasing (\kappa) to embed the orbit makes the worst-case homogeneous Gamma
factor nonintegrable before the first Gamma pole. No stronger radial polynomial weight repairs
this. Remaining possibilities are exactly:

```text
source-selected homogeneous coefficient lies in a slower-growth subspace;
reciprocal weights pair stable and unstable Hatano--Nelson channels;
primitive-flux asymptotics prove flatness without any direct group propagator.       (16)
```

This narrows the finite-to-flat frontier: a uniform polynomial-carrier Hardy theorem cannot be
the missing general-rank proof.

## 7. Hostile audit

1. **Majorant scope explicit.** Nonintegrability of the worst-case distorted density does not
   prove every vector orbit is nonintegrable.
2. **No operator-norm-to-vector lower bound.** The rank wall kills a uniform all-vector theorem,
   not source-selected cancellation.
3. **No source-moment fiction.** Extra regularity of forcing cannot remove a free homogeneous
   component.
4. **No all-rank positive claim.** Concrete window exists only in ranks zero and one.
5. **No low-rank (H^1) overclaim.** Rough primitive transfer and compact-middle remain to be
   proved.
6. **No RH claim.** Higher-rank finite recurrence, exceptional recurrence, completed/raw Evans
   identification, and raw Evans positivity remain.

## 8. Novelty boundary

Power-series summability, Stirling asymptotics, and polynomially weighted lattice propagation are
classical separately. Candidate-new source knowledge is their sharp collision in Suzuki's literal
first-pole strip:

\[
 \text{orbit rank }d
 \to \kappa>d/2
 \quad\text{versus}\quad
 \text{Gamma Hardy }\kappa<\sigma<1
 \to d\le1.                                             \tag{17}
\]

The predecessor corpus contained both polynomial lattice carriers and Gamma-strip decay, but not
threshold `(9)`, dimension wall `(3)`, or the resulting correction of the direct Hardy theorem.
External priority remains unverified.

## Gates

- [x] compute exact polynomially distorted Gamma tail
- [x] prove its (L^1) threshold is `κ < σ`
- [x] combine with lattice threshold `d/2 < κ`
- [x] prove common window exists iff `d <= 1`
- [x] exhibit concrete rank-one window `(κ,σ)=(2/3,3/4)`
- [x] identify uniform radial polynomial Hardy as impossible in rank at least two
- [x] retain vectorwise/biweighted/primitive-flux survivors
- [ ] prove rough primitive one-block transfer in the rank-one window
- [ ] close one-prime compact-middle finite-cell ellipticity
- [ ] prove general-rank source-selected cancellation or primitive finite-to-flat expansion
