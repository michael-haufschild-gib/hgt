# Fixed Taylor Moduli and HT Status Do Not Select Real-Rootedness

- **ID:** `fixed-taylor-modulus-ht-real-rootedness-nonselection`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / HT LANDSCAPE BRIDGE / RH-ROUTE NONSELECTION
- **Scientific status:** `[PROVED HERE] [BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** There is one full-support Taylor-modulus profile supporting both an HT entire function whose complete divisor is real and an HT entire function with a nonreal zero. Thus HT status together with all Taylor magnitudes, Newton data, order, and type cannot select real-rootedness.

## Goal

Strengthen fixed-modulus divisor blindness from “the divisor varies” to the exact qualitative property analogous to RH localization. The result is not a zeta theorem. It classifies the information lost by the quotient

`entire function |-> (HT/DA status, (|a_n|)_n)`.

## Tail-prevalence lemma `[PROVED HERE]`

Let `(r_n)` be positive and satisfy

`limsup_(n->infinity) r_n^(1/n)=0`.                                       `(1)`

For phases `theta=(theta_n)` in the infinite torus `T^N`, put

`F_theta(z)=sum_(n>=0)r_n exp(i theta_n)z^n`.                              `(2)`

Fix any `K>=0` and prescribe arbitrarily the phases `theta_0,...,theta_K`. In the remaining product torus, the phase completions for which `F_theta` is HT over `C(z)` form a dense `G_delta` set of full product Haar measure.

### Proof

Condition (1) makes every series (2) entire. By Mahler's integer-normalization theorem, every DA series satisfies at least one nonzero ADE

`P(z,F,F',...,F^(m))=0`, `P in Z[z,Y_0,...,Y_m]`.                          `(3)`

There are only countably many such `P`.

Fix one `P`, and let `D` be its maximal total `Y`-degree. Generic coefficient extraction gives finite polynomials

`C_(P,N)(X)=[z^N]P(z,F,F',...,F^(m))`.                                    `(4)`

If `D=0`, no series can satisfy `P(z)=0` unless `P` is the zero polynomial, so its solution set is empty. Assume `D>=1`.

The balanced-survival lemma supplies, for every sufficiently large `N`, a nonzero grouped degree-`D` monomial in (4) whose source indices are all `N/D+O_P(1)`. Choose `N` so large that these indices exceed `K`.

After substituting the prescribed prefix coefficients, (4) remains a nonzero polynomial in the tail variables. Indeed, the surviving monomial has tail degree `D` and uses no prefix variable. No other monomial involving a prefix variable can collapse onto it after specialization, because that would have the same tail degree `D` and positive prefix degree, exceeding the maximal total degree `D`.

On the fixed-radius tail torus, this nonzero polynomial becomes a nonzero trigonometric polynomial in finitely many phases: distinct coefficient monomials are distinct Fourier characters, and every `r_n` is nonzero. Its zero set has Haar measure zero and empty interior. This follows directly by induction on the number of variables: regard it as a one-variable Laurent polynomial and apply Fubini outside the lower-dimensional set on which all coefficient polynomials vanish.

The phase set solving the complete ADE (3) is closed and is contained in this nowhere-dense null zero set. Taking the countable union over all integer `P`, the DA phase completions form a meagre Haar-null set. Their complement is dense `G_delta`, has full Haar measure, and consists exactly of HT completions. `square`

## Real-rootedness nonselection theorem `[PROVED HERE]`

There is a positive full-support sequence `(r_n)` and phases `theta`, `phi` such that

1. `F_theta` and `F_phi` are both HT over `C(z)`;
2. their Taylor coefficients have identical moduli `r_n` term by term;
3. every zero of `F_theta` is real;
4. `F_phi` has a nonreal zero.

### Proof

Let `E(z)=1/Gamma(z)`. Every derivative `E^(n)` is a nonzero entire function: otherwise `E` would be a polynomial, contrary to its infinite zero set. The union over `n` of the real zero sets of `E^(n)` is countable. Choose a positive real `x` outside this union and put

`G(z)=E(z+x)=sum_(n>=0)a_nz^n`.                                           `(5)`

Then every `a_n=E^(n)(x)/n!` is real and nonzero. The zeros of `G` are the simple negative real points

`rho_j=-x-j`, `j>=0`.                                                      `(6)`

The function `G` is HT: if `1/Gamma(z+x)` were DA, translation and reciprocal closure of the DA field would make `Gamma` DA, contradicting Hölder's theorem.

Put `r_n=|a_n|`. These radii satisfy (1) because `G` is entire. Thus `G` is one HT member of the fixed-modulus phase fiber and has a completely real divisor.

Now rotate only the constant coefficient:

`G_t(z)=G(z)+(exp(it)-1)a_0`.                                              `(7)`

Every Taylor coefficient of `G_t` has modulus `r_n`. Fix a zero `rho_j`. By the analytic implicit-function theorem, its continuation `rho_j(t)` satisfies

`rho_j'(0)=-i a_0/G'(rho_j)`.                                              `(8)`

Both `a_0` and `G'(rho_j)` are nonzero real numbers, so (8) is nonzero and purely imaginary. Hence `G_t` has a nonreal simple zero for all sufficiently small real `t` of one sign.

Choose such a `t_0`. A small disk around that nonreal zero, disjoint from the real axis, remains a one-zero disk under sufficiently small compact-open perturbations by Rouche's theorem. The map from the phase torus to entire functions is continuous for the compact-open topology: a finite coefficient head is continuous, and (1) makes the uncontrolled tail uniformly small on each fixed compact set. Therefore the set of phases in the same modulus fiber whose function has a nonreal zero contains a nonempty open neighborhood of the phase of `G_(t_0)`.

By the tail-prevalence lemma, HT phases are dense in this fiber. The open neighborhood contains an HT phase `phi`; its function has a nonreal zero and the same coefficient moduli as `G`. Take `theta` to be the phase sequence of `G`. `square`

## Consequences

The two functions have identical:

- Taylor coefficient magnitudes;
- logarithmic Newton polygon and maximum-term function;
- order and type;
- support;
- HT status.

They disagree on real-rootedness. Therefore no selector factoring only through those common data can imply a zero-line statement on the full class of entire functions.

For RH routes, the scope is exact and limited: this excludes only implementations of Hilbert--Polya, Connes, de Branges, Weil, Li, Nyman--Beurling, heat-flow, or coefficient methods that first compress the relevant entire function to this phase-blind quotient. The complete literature criteria retain additional spectral, positivity, norm, heat, Euler, or divisor information and are not excluded by this theorem.

## Why this is not classified as new science

The proof combines Hölder's theorem, countability after Mahler normalization, the elementary zero-set theorem for trigonometric polynomials, Baire/Haar genericity, and the implicit-function theorem. The fixed-modulus and real-rootedness formulation is useful for the project, but the mechanism is a direct genericity bridge rather than a new HT obstruction. No scientific-novelty claim is made.

## Lean status

No Lean formalization is claimed. The complete theorem would require Mahler normalization, generic coefficient extraction and balanced survival, product Haar measure, Baire category, reciprocal-Gamma hypertranscendence, and analytic zero perturbation. None is presently assembled as a whole theorem in the repository.

## Gates

- [x] Complete unconditional paper proof.
- [x] Same full-support moduli and HT status on both sides.
- [x] All-real divisor versus nonreal zero.
- [x] Exact noncategorical RH-route scope.
- [ ] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Proved tail-Haar prevalence of HT phases and constructed one fixed-modulus HT fiber containing both an all-real-zero reciprocal-Gamma translate and an HT member with a nonreal zero.
