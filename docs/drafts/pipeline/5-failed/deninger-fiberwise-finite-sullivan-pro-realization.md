# Fiberwise finite Sullivan pro-realization

- **ID:** `deninger-fiberwise-finite-sullivan-pro-realization`
- **Stage:** 5-failed
- **Type:** LITERATURE-CLOSED REALIZATION NO-GO
- **Former label:** `DAC_FIBERWISE_FINITE_SULLIVAN_PRO_REALIZATION`
- **Parent:** `deninger-relative-sullivan-milnor-character-space`
- **Positive survivor:** `DAC_BAUMSLAG_MILNOR_PRO_REALIZATION`

## Proposed repair

After one-shot realization failed for infinite \(V_F\), filter by
finite-dimensional unit spaces \(U\), realize a relative Sullivan model
\[
 \Lambda(U)\longrightarrow Q_U
 \xrightarrow{\sim}\mathbb Q\oplus U,
\]
and form a fiberwise inverse system over \(X_F\).

## Failure at rank two

Finite-dimensional cohomology does not imply that the minimal Sullivan
generator space is degreewise finite in degree one.  For a wedge of at
least two circles, Sullivan realization agrees with Bousfield--Kan
\(\mathbb Q\)-completion:
\[
 \operatorname{Sul}(S^1\vee S^1)
 \simeq K(\widehat F_{\mathbb Q},1).
\]
Ivanov records that
\[
 H_2(\widehat F_{\mathbb Q};\mathbb Q)\ne0
\]
for a free group \(F\) of rank at least two.  Thus ordinary realization of
the finite-stage model acquires new degree-two cohomology and is not
quasi-isomorphic to \(\mathbb Q\oplus U\).

Zhou's criterion explains the mechanism: the minimal Sullivan algebra of
the nonnilpotent rank-two wedge does not meet the generator-finite-type
condition required for a quasi-isomorphism to forms on its realization.

Therefore finite-unit filtering does not rescue ordinary Sullivan spatial
realization.  The failure occurs before any pro-limit or Deninger descent.

## Positive survivor

Baumslag rationalization behaves differently from Malcev/\(\mathbb
Q\)-completion.  For a finite-rank free group \(F\), it is uniquely
divisible and satisfies
\[
 H_\ast(\operatorname{Bau}(F);\mathbb Q)
 \cong H_\ast(F;\mathbb Q).
\]
Its classifying space therefore has exactly the square-zero rational
cohomology required at a finite unit stage, while its map to the rational
abelianization has a divisible kernel.  This replacement is developed in
`deninger-baumslag-milnor-pro-realization`.

The algebraic filtered-colimit calculation
`DAC_FINITE_UNIT_MILNOR_COLIMIT` survives unchanged; only its proposed
ordinary Sullivan spatial realization fails.

## No-go closure

- **Negative theorem:** rank-two ordinary Sullivan realization already
  creates unwanted \(H^2\).
- **Sharp boundary:** rank zero or one, where no degree-two product must be
  killed.
- **Positive replacement:** Baumslag free rational group packet.
- **Lean status:** realization/group-homology theorem not formalized.

**Verdict:** `FAILED; BAUMSLAG RATIONALIZATION SURVIVES`.

## References

- Sergei O. Ivanov, *An overview of rationalization theories of
  non-simply connected spaces and non-nilpotent groups*, Sections 3, 5,
  and 13: https://arxiv.org/abs/2111.10694
- Jiawei Zhou, *Cohomology of minimal Sullivan algebras of non-finite type
  and their realizations*: https://arxiv.org/abs/2407.20881
