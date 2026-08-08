# Corrected Tate--Floquet Poisson descent

- **ID:** `deninger-corrected-tate-floquet-poisson-descent`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ROUTE-L DERIVED INTERFACE
- **Label:** `DAC_DENINGER_CORRECTED_TATE_FLOQUET_POISSON_DESCENT`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Statement:** derive, before Hilbert completion, the singular endpoint/Fourier detector of the
  canonical Möbius preimage from a strict all-prime Euler--Gamma/Möbius source differential and
  its unsquared Green--Stokes chain identity. Its kernel must be exactly the literal
  Meyer--Poisson boundary range, and its descended geometry must have raw arithmetic weight one
  and real-Fourier compatibility.
- **Source differential status:** closed on paper by
  `DAC_DENINGER_EULER_GAMMA_MOBIUS_CONNECTION_TRANSGRESSION`: strict all-prime-first endpoint,
  physical/Fourier contragredient connection, unsquared covariant Green--Stokes identity, and
  boundary image equal to the Möbius--Fourier commutator.
- **Upstream open premise:** independent arithmetic incidence carrying the fixed resolved
  prime-2/prime-3 Green boundary into the literal Poisson kernel before polarization,
  `XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT`.

## Goal

Specify and close the boundary interface induced by Route L's first genuinely open source gate.
Carrier admission, ordinary and Floquet periodization, positive weight-one cochain energy,
cross-prime Euler strictness, local two-collar Poisson correction, actual Gamma/co-Poisson Hodge
boundary, completed Green primitive, Green transport, conservative admission, physical radial
coefficient, and Calderón--Witt incidence are already constructed. None selects the vanishing
locus.

The strict cofinal defect of the finite gauge-exact Poisson--Kummer connection is now constructed
on paper.  Its non-diagonal unsquared covariant Green--Stokes identity has endpoint exactly the
Möbius--Fourier commutator and annihilates every literal Meyer--Poisson boundary with the exact
kernel below.  The first open operation is narrower: prove from independent arithmetic incidence
that the already-resolved Green boundary lies in this literal kernel before Hermitian
polarization. Constructing another singular target or another Gamma transport does not close that
source-incidence gate.

No divisor, zeta-zero sampling, RH-equivalent positivity premise, abstract Hilbert embedding, or
post-completion projection may enter the construction.

## Fixed source data

Let
\[
 H_-=\mathscr S_{\exp}(\mathbb R),\qquad
 H_\cap=\{f\in\mathscr S(\mathbb R):f\text{ even},\ f(0)=\widehat f(0)=0\},
\]
and let $Z:H_\cap\hookrightarrow H_-$ be Meyer's strict Poisson embedding. Fix a base prime $p$
and ordinary Euler depletion $\Delta_p=1-\tau_{\log p}$. The admitted coefficient is
\[
 \mathcal K_p=\Delta_pH_-,\qquad
 \mathcal B_p=\Delta_pZ(H_\cap),\qquad
 \mathcal K_p/\mathcal B_p\cong M_\zeta.
\tag{1}
\]

For a two-collar pair define
\[
 d_{\mathrm{sec}}(h_+,h_-)(t)
 =e^{t/2}h_+(t)-e^{-t/2}h_-(-t).
\tag{2}
\]
The proved cofinal secondary Floquet energy has exact radical
\[
 \Gamma_{\mathrm{sec}}=\ker d_{\mathrm{sec}}
 =\{(h_+,h_-):h_+(t)=e^{-t}h_-(-t)\}.
\tag{3}
\]
The literal boundary graph is the proper subspace
\[
 \mathcal B_{\mathrm P}
 =\{(Zf,Z\widehat f):f\in H_\cap\}
 \subsetneq\Gamma_{\mathrm{sec}}.
\tag{4}
\]
The classical canonical Möbius preimage
\[
 (\mathfrak M_\mu h)(x)=\sum_{n\ge1}\mu(n)h(\log(nx))
\tag{4a}
\]
is pointwise defined for every $h\in H_-$ and satisfies
$Z(\mathfrak M_\mu h)=h$ on $x>0$. The proved exact range classification is
\[
h\in Z(H_\cap)
\quad\Longleftrightarrow\quad
E\mathfrak M_\mu h\in H_\cap.
\tag{4b}
\]

The critical ordinary prime-circle form is now classified exactly. In half-density coordinates,
after the forced diagonal subtraction,
\[
 \mathcal Q_{\mathrm{Fl}}^{\mathrm{crit}}(u)
 =\sum_{n\ge2}\Lambda(n)
   \bigl(C_u(\log n)+C_u(-\log n)\bigr).
\tag{4c}
\]
This is the centered von Mangoldt prime-power autocorrelation current. It is not positive: for
every nonnegative diagonal prime weighting with nonzero prime-2 weight, compact two-bump sources
give both signs, and the negative source is exactly the matching prime-2 Floquet Euler
coboundary. Thus `(5)` cannot be produced by scalar prime reweighting, vacuum subtraction, or an
orthogonal positive correction to the Floquet energy.

The source tangent is also fixed. On an absolute Euler core,
\[
 -Z_h^{-1}\partial_h Z_h
 =\sum_p\sum_{k\ge1}(\log p)p^{-kh}U_{p^k}.
\tag{4d}
\]
Every finite-prime truncation of `(4d)` is gauge-exact. The missing source object is its strict
cofinal Euler--Gamma/Möbius boundary defect in the enhanced/nuclear topology, together with a
non-diagonal Green--Stokes differential formed before squaring.

## Exact conjecture

`[CONJECTURE] [DAC_DENINGER_CORRECTED_TATE_FLOQUET_POISSON_DESCENT]`

Prove that the explicit upstream all-prime source differential and its Green--Stokes chain
homotopy canonically induce a specified locally convex singular-germ target $\mathscr N_\mu$ and a
continuous boundary operator
\[
 \operatorname{Sing}_{\Gamma/\mathrm{coP},\mu}:
 H_-\longrightarrow\mathscr N_\mu
\tag{5}
\]
satisfying all of the following.

1. **Exact range rigidity**
   \[
   \ker\operatorname{Sing}_{\Gamma/\mathrm{coP},\mu}
   =\{h:E\mathfrak M_\mu h\in H_\cap\}=Z(H_\cap),
   \tag{6}
   \]
   and hence, on the reflected graph,
   $(h,Jh)$ is killed exactly when it belongs to $\mathcal B_{\mathrm P}$.
2. **Strict boundary admission.** The map
   $f\mapsto(Zf,Z\widehat f)$ lands continuously and with closed range in the joint kernel of
   $d_{\mathrm{sec}}$ and `(5)`; no closure replaces the literal range.
3. **Pre-scalar source provenance.** Before any norm square, the upstream source differential,
   the actual Gamma/co-Poisson transport, and `(5)` form a strict Green--Stokes chain-map square.
   Its linear boundary identity annihilates the resolved Green defect. Only after this identity is
   proved may source polarization descend to a closable sesquilinear form
   $\mathcal E_{\mathrm{joint}}$ whose radical is exactly `(4)`, which is invariant under centered
   contragredient flow and has raw arithmetic weight one. The form is not an orthogonal sum of
   diagonal prime-circle energies.
4. **Real-Fourier seam.** Collar exchange induced by $f\mapsto\widehat f$ intertwines `(5)` with
   the source real structure and preserves $\mathcal E_{\mathrm{joint}}$.
5. **Euler transport.** Applying $\Delta_p$ to the physical collar and its canonically reflected
   mate transports `(6)` to the depleted boundary $\mathcal B_p$, independently of the auxiliary
   Floquet prime.
6. **Green--Stokes realization.** Operator `(5)` is the boundary image of the explicit strict
   cofinal source differential, transported through the already-constructed singular
   Gamma/co-Poisson Green chain and the radial origin. It is not an independently postulated
   operator, another construction of the existing transport, a map defined by the desired quotient
   kernel, or a restatement of `(4b)`.
7. **Nuclear, not raw-Hilbert, continuity.** The resulting corrected trace is continuous in the
   Meyer source topology but does not extend as a bounded boundary-annihilating operator on the
   raw Floquet Hilbert completion unless it factors through the resonance quotient.

Equivalently, `(5)` must realize analytically the already-proved set-theoretic incidence
\[
 \Gamma_{\mathrm{sec}}\cap
 \{(h,Jh):E\mathfrak M_\mu h\in H_\cap\}
 =\mathcal B_{\mathrm P}
\tag{8}
\]
and the polarization allowed by clause 3 must descend to a faithful source-derived positive
weight-one form on $M_\zeta$.

## Why this is a derived interface, not the source producer

The following are proved and may not be presented again as missing work:

- strict one-prime admission of the full Meyer quotient;
- ordinary and half-density Floquet exact sequences with Green inverses;
- cofinal prime tomography and finite-prime failure;
- continuous positive-definite all-prime weight-one energy on $H_-$;
- bounded-below ordinary Euler depletion and explicit cross-prime Neumann inverses;
- exact ordinary-versus-twisted Euler leakage dichotomy;
- resonance-only classification of the uncorrected Hilbert quotient;
- bounded raw-Floquet correction no-go;
- scalar and full-circle secondary two-collar Poisson regulators, with exact reflected-graph
  radical;
- classical pointwise Möbius right inversion on every Meyer cochain and exact project-specific classification of the Poisson
  range as its $H_\cap$-regularity domain;
- exact critical Floquet unfolding to the von Mangoldt prime-power autocorrelation current;
- universal positive/negative compact witnesses for every nonnegative diagonal prime weighting;
- actual Gamma/co-Poisson Hodge boundary, Green primitive, Green transport, conservative admitted
  sector, physical radial coefficient, and Calderón--Witt incidence.

Thus neither another ambient energy, another reflection formula, another Gamma transport, nor
another set-theoretic range criterion moves the frontier. The frontier moves only when an explicit
strict all-prime source differential proves the unsquared annihilation identity and induces `(5)`.

## Hard attack program

### A. Descend the strict all-prime gauge defect

The formal corpus proves left Möbius inversion
\[
 \sum_{n\ge1}\mu(n)(Zf)(nx)=f(x),\qquad x>0.
\tag{9}
\]
The right-inverse theorem shows reconstruction is automatic for every $h\in H_-$. What fails is
regular extension at $x=0$: absolute estimates lose Möbius cancellation there. Equation `(4d)`
fixes the prime-power tangent, and every finite Euler gauge is exact. Construct its strict cofinal
Euler--Gamma/Möbius defect in the enhanced/nuclear source, prove the non-diagonal unsquared
Green--Stokes annihilation, and only then identify its boundary image with the endpoint/Fourier
singular germ of `(4a)`. Load-bearing content is source continuity and chain-level cancellation,
not the already-proved set equality `(4b)` or a separately declared singular target.

### B. Use existing secondary regulator as boundary symbol

`DeningerMeyerSecondaryPoissonRegulator.lean` already proves the pointwise two-collar conormal.
`DAC_DENINGER_COFINAL_FLOQUET_SECONDARY_POISSON_GRAPH` upgrades it to the full reflected graph.
The Gamma/co-Poisson incidence in `(5)` must therefore have principal boundary symbol transverse
to `(3)` and must detect precisely the Möbius endpoint/Fourier regularity failure along `(3)`.

### C. Retain jets before closure

The incidence target must retain conormal jets. Zero-order Floquet completion erases all
nonresonant modes and higher jets. Candidate constructions must be tested on exact-multiplicity
Mellin germs before any $L^2$ closure.

## Immediate falsifiers

A candidate fails if any one occurs:

1. its definition uses a zeta zero, Xi divisor, quotient projection, or assumed positive Meyer
   pairing;
2. it factors boundedly through the raw Floquet Hilbert completion;
3. it kills all of $\Gamma_{\mathrm{sec}}$ rather than exactly `(4)`;
4. it only samples finitely many prime circles;
5. it replaces $\mathcal B_{\mathrm P}$ by its Hilbert closure;
6. it loses the opposite Fourier collar or does not commute with collar exchange;
7. it proves endpoint identities without a global nuclear-domain estimate;
8. it defines a maximal domain or singular target by restating `(4b)`, with no source Green
   construction;
9. it is a diagonal prime-weighted circle norm, a vacuum subtraction, or a positive orthogonal
   correction of such a norm;
10. it reconstructs the already-existing Gamma/co-Poisson Green transport without supplying the
    upstream all-prime source differential and its unsquared annihilation identity.

## Gates

- [x] 0 → 1 in-progress: exact object, dependencies, topology, and falsifiers fixed
- [x] upstream source differential: strict all-prime Euler--Gamma/Möbius transgression, exact
  Gamma/co-Poisson boundary image, and literal-boundary Green--Stokes annihilation proved on paper
- [ ] upstream RH-bearing incidence: `XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT`
- [ ] 1 → 2 fully-proven: derive `(5)` from that source differential and prove `(6)`--`(8)`
  unconditionally
- [ ] 2 → 3 formalized: paused until Lean corpus refactor ends
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-08 — Reoriented from generic relative Hodge form to corrected Tate--Floquet descent.
- 2026-08-08 — Exact resonance quotient and bounded-correction no-go proved.
- 2026-08-08 — Existing scalar secondary regulator lifted cofinally; exact reflected-graph radical
  proved. Open core narrowed to Gamma/co-Poisson Poisson-range incidence `(6)`.
- 2026-08-08 — Canonical Möbius transform proved to be a pointwise right inverse on every Meyer
  cochain; range incidence reduced exactly to its endpoint/Fourier regularity. Open core narrowed
  again to source Green--Stokes realization of that singular regularity defect.
- 2026-08-08 — Reclassified as downstream interface. Critical Floquet subtraction was identified
  exactly with the von Mangoldt prime-power current, while a universal compact two-bump theorem
  proved every nonnegative diagonal prime weighting indefinite. Updated Hellinger/Lean audit found
  actual Gamma/co-Poisson Green transport and Calderón--Witt incidence already constructed. First
  source gate moved upstream to strict cofinal Euler--Gamma/Möbius gauge-defect sewing and its
  non-diagonal unsquared Green--Stokes annihilation identity.
- 2026-08-08 — `DAC_DENINGER_EULER_GAMMA_MOBIUS_CONNECTION_TRANSGRESSION` constructed the
  all-prime-first source family, proved its strict PNT endpoint, derived the forced
  physical/Fourier connection difference and unsquared covariant identity, and identified its
  endpoint boundary image with the Möbius--Fourier commutator.  Remaining upstream premise is no
  longer construction of that source operation; it is independent arithmetic incidence of the
  fixed resolved two-prime Green boundary in the literal kernel.
