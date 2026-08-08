# Deninger source--Poisson chain-lift obstruction

- **ID:** `deninger-source-poisson-chain-lift-obstruction`
- **Stage:** 2-fully-proven
- **Type:** ROUTE-L EXACT OBSTRUCTION / CANONICAL PRELIFT
- **Canonical label:** `DAC_DENINGER_SOURCE_POISSON_CHAIN_LIFT_OBSTRUCTION`
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW SYNTHESIS] [NOT RH]`
- **Lean status:** intentionally paused during corpus refactor
- **Parents:**
  - `deninger-mobius-fourier-commutator-poisson-kernel.md`;
  - `deninger-euler-gamma-mobius-connection-transgression.md`;
  - `deninger-two-prime-oriented-boundary-wall.md`.

## Purpose

The open Route-L source theorem was phrased as construction of maps

\[
 \mathcal R_1:C^1_{\rm rel}\to H_\cap,
 \qquad
 \mathcal R_2:C^2_{\rm rel}\to H_-,
 \qquad
 \mathcal R_2D=Z\mathcal R_1.
\tag{1}
\]

This phrasing leaves a fake degree of freedom: once the degree-two Gamma/Calderón realization is
fixed, the degree-one lift is not an object to guess. Canonical Möbius inversion already constructs
its only source-compatible candidate on the positive radial ray. The missing theorem is exactly
vanishing of one explicit opposite-collar Fourier obstruction.

## Setup

Let

\[
 C^1_{\rm rel}\xrightarrow{D}C^2_{\rm rel}
\]

be a rational-Witt/Milnor relevant-complex sector, and let

\[
 \mathcal G_\Gamma:C^2_{\rm rel}\longrightarrow H_-
\]

be any fixed linear degree-two realization in the Meyer cochain source whose
\(\mathfrak S_\mu\)-image is compared with the actual singular Gamma/co-Poisson boundary. For
\(h\in H_-\), write

\[
 f_h(x)=\sum_{n\ge1}\mu(n)h(\log(nx)),\qquad x>0,
\]

and let \(Ef_h\) be its even \(L^1\)-extension. Existing unconditional PNT cancellation proves
that \(Ef_h\) has every polynomial moment and zero mass. Define

\[
 \mathcal P_\Gamma(w)=Ef_{\mathcal G_\Gamma(Dw)}
 \in L^1_{\rm even}(\mathbb R),
\tag{2}
\]

and the source--Poisson lifting obstruction

\[
 \boxed{\quad
 \Omega_{\mu,\Gamma}
   =\mathfrak S_\mu\mathcal G_\Gamma D,
 \qquad
 \Omega_{\mu,\Gamma}(w)
   =\mathcal F\mathcal P_\Gamma(w)
      -Ef_{J\mathcal G_\Gamma(Dw)}.
 \quad}
\tag{3}
\]

It is defined before divisor specialization and without a Hilbert completion, quotient-selected
domain, or choice of a putative lift.

## Theorem (canonical chain-lift obstruction)

For every \(w\in C^1_{\rm rel}\), the following are equivalent:

1. \(\Omega_{\mu,\Gamma}(w)=0\);
2. \(\mathcal G_\Gamma(Dw)\in Z(H_\cap)\);
3. the canonical prelift \(\mathcal P_\Gamma(w)\) extends through the radial origin to an element
   of \(H_\cap\), its opposite collar is its Fourier transform, and
   \[
      Z\mathcal P_\Gamma(w)=\mathcal G_\Gamma(Dw);
   \tag{4}
   \]
4. the value \(\mathcal G_\Gamma(Dw)\) admits a Meyer--Poisson chain lift through \(Z\).

Consequently, on any source subspace \(V\subset C^1_{\rm rel}\), equation `(1)` with
\(\mathcal R_2=\mathcal G_\Gamma\) holds for the canonical choice
\(\mathcal R_1=\mathcal P_\Gamma\) exactly when

\[
                  \Omega_{\mu,\Gamma}|_V=0.
\tag{5}
\]

### Proof

The exact Möbius--Fourier kernel theorem gives

\[
       \ker\mathfrak S_\mu=Z(H_\cap).
\]

Applied to \(h=\mathcal G_\Gamma(Dw)\), this proves `1 ↔ 2`. Pointwise Möbius inversion gives
`(4)` on the positive ray for every \(w\), before any regularity assertion. If `(3)` vanishes,
the opposite Möbius collar supplies every Fourier moment; Fourier inversion makes
\(\mathcal P_\Gamma(w)\) smooth through zero and Schwartz. Poisson summation then forces its value
and Fourier value at zero to vanish. This is precisely membership in \(H_\cap\), proving
`1 → 3`. Boundary inclusion in the exact-kernel theorem proves `3 → 1`.

Clause `3` gives `4`. Conversely any \(H_\cap\)-lift puts the target value in \(Z(H_\cap)\), so
`4 → 2`. Linearity gives `(5)`. ∎

## Sharp two-prime audit for a coefficient-faithful specialization

Let

\[
 w_{23}=H(j_2(1)-j_3(1)),
 \qquad Dw_{23}=j_2(1)-j_3(1).
\]

The required coefficient-faithful comparison for a proposed
\(\mathcal G_{\Gamma,\rho}\) at a Xi divisor point \(\rho\) is

\[
 \boxed{\quad
 \operatorname{Ev}_\rho\bigl(\Omega_{\mu,\Gamma}(w_{23})\bigr)
   =c_\rho\bigl(g_2(\rho)-g_3(\rho)\bigr),
 \qquad c_\rho\ne0.
 \quad}
\tag{6}
\]

Therefore

\[
 \Omega_{\mu,\Gamma}(w_{23})=0
 \quad\Longrightarrow\quad
 \operatorname{Re}\rho=\frac12.
\tag{7}
\]

Thus any proposed degree-two realization satisfying `(6)` has the sharp consequence `(7)`.
Universal vanishing on actual Xi divisor fibres proves RH. This theorem does not assert either
the realization/comparison `(6)` or the vanishing; `(6)` is its endpoint audit.

## Scientific consequence

Route L no longer needs to search for an abstract degree-one lift. It has a canonical candidate
with unconditional \(L^1\), all-moment, zero-mass, and positive-ray right-inverse properties.
After the actual degree-two realization and comparison `(6)` are constructed, exact missing
scientific knowledge is source-derived identity

\[
                  \Omega_{\mu,\Gamma}(w_{23})=0
\tag{8}
\]

or a stronger resolved-family version, proved before divisor specialization. Equivalently, one
must prove that the two canonical Möbius collars of the actual rational-Witt/Milnor boundary are
Fourier partners. More completion, positivity, source exactness, or a freely chosen preimage does
not address `(8)`.

This also exposes required nonseparability. Existing vertical Milnor/Koszul incidence is exact,
and its completed all-cross-prime differential leaves the full scalar Xi line. Existing
Euler/Cartan and prime-packet connections are flat. Hence `(8)` must come from a genuinely
horizontal, source-derived prime--depth--divisor relation, singular same-grade transgression, or
independent arithmetic support-exclusion law. It cannot be generated by the already-closed
vertical differential alone.

## Hostile audit

1. `(3)` is not defined by its desired kernel; it is the fixed Möbius--Fourier commutator applied
   to the fixed source boundary realization.
2. `(6)` is the required coefficient-faithful comparison hypothesis, not a conclusion smuggled
   into the obstruction theorem. It retains both prime labels and nonzero leading Xi jet.
3. The theorem does not infer `(8)` from source exactness. It proves exact equivalence between
   `(8)` and the missing chain lift.
4. Canonical Möbius prelift is not claimed to be Schwartz. That regularity is exactly what
   obstruction detects.
5. General factorization-through-a-kernel algebra is parent mathematics. Corpus-new content is
   identification of Route L's proposed chain map with this explicit opposite-collar defect and
   elimination of arbitrary lift construction from the frontier.

## Gates

- [x] canonical degree-one prelift on every source boundary
- [x] unconditional all-moment and zero-mass domain
- [x] exact lift-obstruction equivalence
- [x] sharp endpoint implication for every realization satisfying fixed two-prime Xi-jet audit
- [ ] construct/identify actual degree-two relevant-complex realization satisfying that audit
- [ ] source-derived proof of `(8)`
- [ ] RH
