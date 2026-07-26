# Exact-\(\pi_1\)-preserving Milnor correction

- **ID:** `deninger-exact-pi1-preserving-milnor-correction`
- **Stage:** 5-failed
- **Type:** PAPER-PROVED TOPOLOGICAL NO-GO
- **Parent:** `deninger-baumslag-milnor-pro-realization`
- **Positive survivor:** divisible-kernel finite-cover invariance

## Proposed shortcut

Use a \(\pi_1\)-fiberwise rationalization or another modification that keeps
the finite-stage character torus fundamental group exactly unchanged while
trying to replace
\[
 H^\ast(T^m;\mathbb Q)=\Lambda^\ast(\mathbb Q^m)
\]
by the square-zero Milnor algebra
\[
 \mathbb Q\oplus\mathbb Q^m[-1].
\]

## No-go theorem

Let \(X\) be a connected CW complex with
\(\pi_1(X)\cong\mathbb Z^m\), \(m\ge2\).  Then
\[
 H^2(X;\mathbb Q)\ne0.                                               \tag{1}
\]
Consequently no such \(X\) has rational cohomology algebra
\(\mathbb Q\oplus\mathbb Q^m[-1]\).

## Proof

Hopf's exact sequence gives a surjection
\[
 H_2(X;\mathbb Q)\twoheadrightarrow
 H_2(\pi_1(X);\mathbb Q).                                            \tag{2}
\]
For \(\pi_1(X)=\mathbb Z^m\),
\[
 H_2(\mathbb Z^m;\mathbb Q)
 \cong\Lambda^2(\mathbb Q^m)\ne0
\]
when \(m\ge2\).  Thus \(H_2(X;\mathbb Q)\ne0\).  Over a field, the universal
coefficient theorem identifies
\[
 H^2(X;\mathbb Q)
 \cong\operatorname{Hom}_{\mathbb Q}(H_2(X;\mathbb Q),\mathbb Q),
\]
which proves `(1)`.

## Consequences for Deninger's coefficient

The finite-unit torus model cannot be corrected to square-zero Milnor
cohomology while preserving its fundamental group exactly.  In particular,
the standard \(\pi_1\)-fiberwise rationalization—which by definition leaves
\(\pi_1\) unchanged—is not the required operation.

The correction must instead fit an exact sequence
\[
 1\longrightarrow K_U\longrightarrow
 \pi_1(X^M_{F,U})\longrightarrow\pi_1(X_F)\longrightarrow1
\]
with nontrivial kernel.  To preserve arithmetic finite covers, \(K_U\)
must be invisible to finite groups.  A connected divisible/prounipotent
kernel does exactly this by
`DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE`.

This proves that the divisible kernel in
`DAC_BAUMSLAG_MILNOR_PRO_REALIZATION` is necessary, not merely a
convenient sufficient device.

## No-go closure

- **Negative theorem:** exact \(\pi_1\) preservation is incompatible with
  square-zero \(H^{\ge2}\) once two independent unit classes are present.
- **Sharp boundary:** \(m=1\), where
  \(\Lambda^2(\mathbb Q)=0\).
- **Positive replacement:** change \(\pi_1\) by a divisible kernel and
  preserve its profinite completion/finite-cover category instead.
- **Lean status:** Hopf exact sequence is not currently available in the
  project; finite-quotient invisibility of divisible groups is already
  formalized by
  `Bottcher.monoidHom_eq_one_of_powerDivisible_finite_codomain`.

**Verdict:** `FAILED; DIVISIBLE-KERNEL REPLACEMENT FORCED`.

## References

- Heinz Hopf, *Fundamentalgruppe und zweite Bettische Gruppe*.
- Kenneth S. Brown, *Cohomology of Groups*, Hopf exact sequence.
- Sergei O. Ivanov, *An overview of rationalization theories of
  non-simply connected spaces and non-nilpotent groups*, Section 12:
  https://arxiv.org/abs/2111.10694
