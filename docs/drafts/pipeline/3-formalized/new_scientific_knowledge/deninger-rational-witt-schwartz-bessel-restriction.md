# Rational-Witt radial-Schwartz Bessel restriction

- **ID:** `deninger-rational-witt-schwartz-bessel-restriction`
- **Stage:** 3-formalized
- **Type:** SOURCE-TO-PACKET GLOBAL BESSEL CONSTRUCTION
- **Label:** `DAC_DENINGER_WRAT_SCHWARTZ_BESSEL_RESTRICTION`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** the radial Schwartz factor already present in Deninger's/Meyer's source, combined
  with polarized half-density and the canonical first suspension transgression, supplies a
  continuous all-prime Hilbert restriction for every uniformly bounded rational-Witt packet
  field. No independently selected target weight is inserted.

## 1. Problem left by finite rational-Witt visibility

For every prime \(p\), finite Frobenius stages are cofinal and Haar-\(L^2\)-dense in the packet
\[
 B_p=\operatorname{Aut}(\overline{\mathbb F}_p^\times)/
       \overline{\langle\operatorname{Frob}_p\rangle},
\]
and every finite-stage function has an arithmetic-Frobenius-fixed witness in
\(\mathbb C\otimes W_{\rm rat}(\overline{\mathbb F}_p)\). The canonical first circle character
then gives an isometric positive-mode transgression
\[
 T_p:L^2(B_p)\longrightarrow
 L^2\!\left(B_p\times\mathbb R/\log p\,\mathbb Z\right).
\]

Neither theorem is global. A raw coordinate with a cofinite positive packet-norm floor is not
Bessel, and even the graph-Green weight \((\log p)^{-2}\) does not make its scalar mass summable.
The missing decay must therefore come from the source coefficient topology.

## 2. Source-forced restriction

Let \(a_p\in L^2(B_p)\) be a packet field with
\[
 \|a_p\|\le B\qquad(p\ \text{prime}).
\]
For \(f\in\mathcal S(\mathbb R,\mathbb C)\), define
\[
 \boxed{\;
 \mathcal R_a(f)_p
   =p^{-1/2} f(p)\,T_p(a_p).
 \;}                                                               \tag{1}
\]

Both scalar factors in `(1)` are forced before any Hilbert target is chosen.

1. If the descended radial coordinate has value \(1\), the degree-\(p\) discrete flow pullback is
   exactly \(f(p)\), by the already-proved identity
   \(f(\phi^{\log p}x)=f(p\,x)\).
2. The factor \(p^{-1/2}\) is the polarized half-density normalization forced by
   push--pull degree \(p\), projection-formula adjunction, and Hodge naturality.
3. \(T_p\) is the canonical first suspension Fourier mode, not an arbitrary local embedding.

Thus `(1)` is radial source multiplication followed by source power transport. It is not a family
of target weights chosen to repair convergence.

## 3. Exact Bessel theorem

Let
\[
 q_{1,0}(f)=\sup_{x\in\mathbb R}|x|\,|f(x)|
\]
be the first zeroth-derivative Schwartz seminorm. Since \(p|f(p)|\le q_{1,0}(f)\) and \(T_p\) is
isometric,
\[
 \|\mathcal R_a(f)_p\|
   =p^{-1/2}|f(p)|\,\|a_p\|
   \le Bq_{1,0}(f)\,p^{-3/2}.                                     \tag{2}
\]
Consequently
\[
 \sum_p\|\mathcal R_a(f)_p\|^2
 \le B^2q_{1,0}(f)^2\sum_p p^{-3}<\infty.                          \tag{3}
\]
The final convergence follows by restriction of the ordinary \(3\)-series on \(\mathbb N\); no
prime-number theorem is used.

Put
\[
 M_3=\sum_p p^{-3}.
\]
Equation `(3)` gives the continuous complex-linear map
\[
 \mathcal R_a:\mathcal S(\mathbb R,\mathbb C)\longrightarrow
 \bigoplus_p^{\ell^2}
 L^2\!\left(B_p\times\mathbb R/\log p\,\mathbb Z\right),
\qquad
\|\mathcal R_a(f)\|\le B\sqrt{M_3}\,q_{1,0}(f).                    \tag{4}
\]

This is the missing global Bessel estimate on the separated radial--Wrat first-mode sector. Raw
Wrat data alone still fail, exactly as the prior obstruction requires; multiplication by a radial
Schwartz source section is what changes the domain.

## 4. Global Green form and exact radical

Pull `(4)` into the already-constructed full-block prime Green form
\[
 G(x,x)=\sum_p(\log p)^{-2}\|x_p\|^2.
\]
Then
\[
 G_a(f,f)
 =\sum_p(\log p)^{-2}
   \bigl(p^{-1/2}|f(p)|\,\|a_p\|\bigr)^2\ge0.                       \tag{5}
\]
Faithfulness of the block form and injectivity of \(T_p\) give the exact radical
\[
 G_a(f,f)=0
 \quad\Longleftrightarrow\quad
 \forall p,\ f(p)=0\ \text{or}\ a_p=0.                             \tag{6}
\]

Clause `(6)` is deliberately not relabelled as the arithmetic boundary theorem. Route L still
must prove that the relevant complex's middle boundaries have exactly this joint sampling kernel
on the separated sector, and then control nonseparated cup/cross-prime terms.

## 5. Actual finite Wrat admission

Fix one prime \(p\), a nonzero finite packet function \(F\), and extend its Haar-\(L^2\) vector by
zero to all other primes. If \(f(p)\ne0\), then `(5)` is strictly positive. The earlier rational-Witt
bridge supplies \(w\) in the finite cyclotomic Wrat algebra such that

- \(w\) is fixed by arithmetic Frobenius after inclusion in the published complexified Wrat
  presentation;
- every finite packet evaluation of \(w\) equals \(F\);
- the radial-damped global first-mode Green energy is positive.

Therefore the construction is not an abstract Hilbert majorant: every local finite Wrat mode enters
its global domain through an actual source witness and finite-prime extension by zero.

## 6. Hostile audit

- **Not arbitrary damping.** \(f(p)\) is the literal discrete-flow radial pullback; \(p^{-1/2}\)
  is forced by polarized degree.
- **Not `Wrat = coefficient`.** Wrat supplies packet geometry/evaluations. Schwartz radial
  sections belong to the leafwise analytic coefficient. Their product is formed only after those
  roles are separated.
- **Not a proof of the full relevant complex.** `(4)` closes Bessel continuity on the separated
  radial--finite-Wrat first-mode sector. Sheafified arithmetic descent and boundary
  classification remain.
- **Not a scalar packet average.** Each entire Haar-\(L^2(B_p)\) block survives.
- **Not RH-equivalent input.** No Xi divisor, zeta zero, positivity assumption, or numerical
  computation occurs.
- **No hidden prime theorem.** The majorant is the ordinary convergent \(3\)-series restricted to
  primes.

## 7. Novelty audit

Primary-source search found the ingredients separately:

- Deninger's rational-Witt dynamical system and closed prime orbits;
- Deninger's polarized weight/half-density formalism;
- Meyer's nuclear Schwartz source and dilation/summation operator.

No located primary source states the combined all-prime operator `(1)`, its prime-cubic bound
`(2)`--`(4)`, the exact Green radical `(6)`, or actual finite-Wrat admission into that domain.
Repository search likewise found only the separate Wrat visibility, first-mode, graph-Green, and
raw-packet no-go modules. This card's new content is their source-forced global interface.

## 8. Lean status

Formalized unconditionally in
`GaloisForLFunctions/RHTower/Deninger/DeningerRationalWittSchwartzBesselRestriction.lean`:

1. `summable_deningerPrimeCubicMass` proves prime-cubic summability;
2. `summable_norm_deningerSchwartzFirstModeRestrictionValue_sq` constructs the dependent
   all-prime Hilbert vector;
3. `deningerSchwartzFirstModeRestrictionCLM` proves continuity with bound `(4)`;
4. `deningerSchwartzFirstModeRestriction_eq_zero_iff` and
   `deningerSchwartzFirstModeGreenEnergy_eq_zero_iff` prove `(5)`--`(6)`;
5. `deningerFiniteRationalWitt_exists_witness_pos_globalGreenEnergy` gives the actual
   arithmetic-Frobenius-fixed Wrat witness with positive global energy.

The proofs use no computation, `sorry`, `axiom`, `opaque`, or conditional mathematical
assumption.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  https://arxiv.org/abs/math/0412277.

## Log

- 2026-08-02 — Exact source-derived restriction conjectured; dependency audit separated it from
  the previously retired `Wrat = coefficient` route.
- 2026-08-02 — Scratch Lean certificate proved prime-cubic Bessel bound, continuous map, exact
  Green radical, and finite-Wrat positive admission.
- 2026-08-02 — Permanent module passed direct Lean elaboration; card promoted to Stage 3.
