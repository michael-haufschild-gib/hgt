# Invented rational-Witt correspondence topos

- **ID:** `deninger-rational-witt-correspondence-topos`
- **Stage:** 5-failed
- **Type:** FALSIFIED SOURCE ATTRIBUTION
- **Label:** `DAC_WRAT_CORRESPONDENCE_TOPOS_REALIZATION_NO_GO`
- **Parent:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Statement:** Deninger's rational-Witt correspondence theorem does
  not define a new correspondence category or topos.

## Exact killing mechanism

Deninger's 2025 Theorem 5.1 proves, for normal Noetherian affine \(X\),
\[
 W_{\mathrm{rat}}(\mathcal O(X))
 \cong
 \underline{\operatorname{Corr}}(X,\mathbb A^1),                  \tag{1}
\]
where the right side is the standard Suslin--Voevodsky group of finite
relative correspondences from \(X\) to \(\mathbb A^1\), modulo the
zero section.  Proposition 5.2 identifies Frobenius and Verschiebung
with pushforward and pullback along
\(\pi_n:x\mapsto x^n\).

Formula `(1)` identifies one represented coefficient in the already
defined finite-correspondence category.  It does not construct:

- a category \(\mathsf{WCor}(X_0)\);
- a new Grothendieck topology;
- a dimension-one rational-Witt topos;
- a Milnor--Witt enhancement;
- an analytic realization on Deninger's suspension.

Deninger's statement that stronger descent may remedy defects of the
2024 dynamical spaces is explicitly a proposed research direction, not
any of these constructions.

## No-go closure

- **Exact killing theorem/mechanism:** Theorem 5.1 represents
  \(W_{\mathrm{rat}}\) by the single target \(\mathbb A^1\) inside the
  standard correspondence category; it supplies no new category or
  topos.
- **Strongest positive survivor:** use the standard
  Suslin--Voevodsky finite-correspondence category and the represented
  coefficient
  \[
    \mathbb Z_{\mathrm{tr}}(\mathbb A^1)/
      \mathbb Z_{\mathrm{tr}}(0).
  \]
  Its power-map push/pull operations are exactly \(F_n,V_n\).
- **New insight:** arithmetic dimension comes from the regular
  one-dimensional base and its Rost--Schmid complex, not from a
  claimed dimension of a Witt topos.  The remaining bridge is an
  analytic realization of a transfer coefficient on Deninger's
  invariant sheaf.
- **Status:** source correction complete.  Positive survivor continues
  as `DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION`.

## References

- Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  Theorem 5.1 and Proposition 5.2:
  https://arxiv.org/abs/2508.05329
- Andrei Suslin and Vladimir Voevodsky, *Relative cycles and Chow
  sheaves*: https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/relativecycles.pdf

## Log

- 2026-07-26 — Retired after checking exact scope of Deninger's
  finite-correspondence theorem.
