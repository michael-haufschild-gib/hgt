# Flat Suzuki primitive flux is exponentially small without a prime-group bound

- **ID:** `suzuki-flat-primitive-flux-volterra-liouville`
- **Stage:** 2-fully-proven
- **Type:** BLOCK LIOUVILLE THEOREM / ARBITRARY-NONNORMAL FLAT-SECTOR CLOSURE
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-primitive-flux-nonnormal-graph-reduction.md`,
  `suzuki-coordinate-cutoff-primitive-flux-identity.md`,
  `suzuki-gamma-wall-block-hardy-and-derivative-scattering.md`,
  `suzuki-interior-seam-indicial-dipole-exclusion.md`

## 1. Result

The primitive-flux formulation closes the all-orders-flat **value/flux** sector for an arbitrary
bounded nonnormal prime adjacency. No polynomial bound on \(\exp(-ixB)\) is needed.

Let \(X\) be a complex Hilbert space and consider, on a terminal ray,

```text
A F-Y=G,
Y'=D F-H,                                               (1)

A=2L I+R-B.                                             (2)
```

Here:

1. \(R\) is the literal componentwise Gamma jump;
2. \(B\in\mathcal B(X)\) is arbitrary;
3. \(D\) is a bounded block operator whose physical kernel has exponential off-block decay. The
   paired Suzuki value/logistic/polar block \(D=2I-Z\) has this property;
4. for some \(0<\delta<1\), the unit-block norms of \(G,H\) are
   \(O(e^{-\delta n})\);
5. \(F\) is all-orders flat in unit-block \(L^2\):

```text
for every N,  ||F||_(L2([n,n+1];X))=O_N(n^(-N));        (3)
```

Then, for every \(0<\delta'<\delta\),

```text
exp(delta' L)F in L2,
exp(delta' L)Y in H1.                                  (4)
```

For the literal Gamma/logistic kernels, \(\delta\) may be any number below one whenever the
primitive and zero-order sources have the corresponding Gamma weight. Thus a finite-recurrence
Suzuki flat sector enters every prescribed smaller strip:

```text
all finite inverse-log charges vanish
+ primitive source at weight delta<1
 -> exp(delta' L)(F,Y) in L2,       delta'<delta.       (5)
```

This proves `SUZUKI-PRIMITIVE-FLUX-LIOUVILLE`. It does **not** yet prove
\(e^{\delta'L}F'\in L^2\); Section 7 isolates that remaining source-specific propagation theorem.

## 2. Gamma block localization

Let \(I_n=[n,n+1]\). Choose translates \(\chi_n\) of one smooth cutoff, equal to one on \(I_n\)
and supported in \([n-1,n+2]\). The exact Gamma kernel gives

```text
([R,chi_n]F)(L)
 =integral_0^infinity
   [(chi_n(L)-chi_n(L+s))F(L+s)
    +(chi_n(L)-chi_n(L-s))F(L-s)]
   /(exp(s)-1) ds.                                     (6)
```

For \(0<s<1\), the cutoff difference is \(O(s)\), cancelling the denominator. For \(s\ge1\),
the kernel is \(O(e^{-s})\). Young's inequality therefore gives, for some \(\mu>0\),

```text
||[R,chi_n]F||_2
 <=C sum_m exp(-mu|n-m|)||F||_(L2(I_m)).                (7)
```

This is the translated unit-block form of the proved Gamma cutoff-commutator estimate. The same
bound holds for the logistic block and every exponentially localized polar/cutoff remainder.

Put

```text
f_n=||F||_(L2(I_n)),
y_n=||Y||_(L2(I_n)),

(E a)_n=sum_m exp(-mu|n-m|)a_m.                         (8)
```

Localize the first equation in `(1)`:

```text
A(chi_n F)=chi_n(Y+G)+[R,chi_n]F.                       (9)
```

Since \(R\ge0\) on the real line,

```text
Re inner(A v,v)
 >=[2(n-1)-||B||]||v||^2                               (10)
```

for \(v\) supported in \([n-1,n+2]\). Pair `(9)` with \(\chi_nF\), use `(7)`, and then apply the
positive exponential envelope \(E\). For all sufficiently large \(n\), the \(E f\) term is
absorbed by the growing factor \(2n\). The finite shift in \(n\), and all blocks below the
terminal threshold, contribute \(O(e^{-\mu n})\). Hence

```text
(E f)_n
 <=A_0 n^(-1)(E y)_n+C_0 exp(-delta_0 n),              (11)
```

where any \(\delta_0<\min(\delta,\mu)\) is allowed. No adjoint or group bound for \(B\) occurs.

## 3. Flatness makes zero charge automatic and gives the backward Volterra tail

The second equation in `(1)` gives \(Y'=DF-H\). Assumption `(3)` and the exponential source make
\(Y'\) integrable with every polynomial weight. Therefore \(Y(L)\) has a terminal limit.

That limit is automatically zero.  The first equation and the localized Gamma estimate give

```text
||Y||_(L2(I_n))
 <=2(n+1)||F||_(L2(I_n))
   +C(E||F||)_n+||B||||F||_(L2(I_n))+||G||_(L2(I_n)).  (11a)
```

Superpolynomial flatness gives `n||F||_(L2(I_n))->0`; its exponential envelope is again
superpolynomially flat; and `G` is exponentially small.  Hence the right side of `(11a)` tends to
zero.  Strong convergence `Y(L)->Y_infinity` makes the left side tend to `||Y_infinity||`, so
`Y_infinity=0`.  This hypothesis discharge is proved separately in
`suzuki-flat-flux-charge-automaticity.md`.  Therefore

```text
Y(L)=-integral_L^infinity [D F(t)-H(t)]dt.              (12)
```

The exponential off-block kernel of \(D\), Cauchy--Schwarz on every unit interval, and `(12)`
give

```text
(E y)_n
 <=D_0 sum_(m>=n-2)(E f)_m+C_1 exp(-delta_0 n).         (13)
```

Substitute `(11)` into `(13)` and absorb the harmless two-index displacement:

```text
q_n
 <=A_1 sum_(m>=n) q_m/m+C_2 exp(-delta_1 n),            (14)

q_n=(E y)_n,
```

for every fixed \(\delta_1<\delta_0\). Assumption `(3)`, equation `(12)`, and the source bounds
show that \(q_n=O_N(n^{-N})\) for every \(N\).

## 4. Flat Volterra lemma

### Lemma

Let \(q_n\ge0\) be superpolynomially decreasing and suppose, for all sufficiently large \(n\),

```text
q_n<=A sum_(m>=n)q_m/m+C exp(-delta n).                 (15)
```

Then

```text
q_n=O_delta'(exp(-delta' n))
```

for every \(0<\delta'<\delta\).

### Proof

Put

```text
Q_n=sum_(m>=n)q_m/m.                                    (16)
```

The sum converges by superpolynomial decay, and \(n^NQ_n\to0\) for every \(N\). From
\(Q_{n+1}=Q_n-q_n/n\) and `(15)`,

```text
Q_(n+1)
 >=(1-A/n)Q_n-C exp(-delta n)/n.                        (17)
```

Choose \(n_0>A\) and define

```text
p_(n_0)=1,
p_(n+1)=(1-A/n)p_n.                                    (18)
```

Then \(p_n>0\) and \(p_n\asymp n^{-A}\). Divide `(17)` by \(p_{n+1}\):

```text
Q_(n+1)/p_(n+1)
 >=Q_n/p_n
   -C exp(-delta n)/(n p_(n+1)).                        (19)
```

Iterate from \(n\) to \(N\). Superpolynomial decay gives
\(Q_N/p_N\to0\). Letting \(N\to\infty\) yields

```text
Q_n
 <=C p_n sum_(m>=n)
      exp(-delta m)/(m p_(m+1)).                        (20)
```

Since \(p_n/p_{m+1}\le C[(m+1)/n]^A\), an exponential tail absorbs this polynomial ratio. Hence
\(Q_n=O(e^{-\delta'n})\) for every \(\delta'<\delta\). Equation `(15)` gives the same bound for
\(q_n\). `QED`

## 5. Completion of the flux theorem

Apply the lemma to `(14)`. Then \(E y\), hence \(y\), decays at every smaller exponential rate.
Equation `(11)` gives the same conclusion for \(f\). Summing unit blocks proves

```text
exp(delta' L)F,
exp(delta' L)Y in L2.                                  (21)
```

Finally \(Y'=DF-H\), and the exponentially localized block bound for \(D\) preserves every
strictly smaller weight. Therefore

```text
exp(delta' L)Y' in L2,                                 (22)
```

which proves `(4)`. `QED`

## 6. Consequence for finite-recurrence Suzuki assembly

The physical-orbit carrier is bounded and tempered. After subtracting all finite conormal
descendants, its residual flat sector satisfies `(3)`. The primitive-cutoff theorem supplies

```text
G=[R-B,M]F,
H=M'(2L+R-B)F+[Z,M]F+M H_original,                     (23)
```

with \(G,H\) in every prescribed weight below one at finite recurrence type. Its exact augmented
equation is `(1)`.

The paired indicial theorem removes the terminal value/dipole flux charge at every interior seam.
At physical roots the zero exterior orientation has only the half-log indicial root; its
borderline `1/log` dipole produces an uncancelled logarithmic source and is zero against the
bounded completed source. Moreover the flat terminal charge is automatic by `(11a)`. Literal
source assembly is now proved; optional low-frequency counterterms lie in the same subcritical
class. No independent physical dipole or flat-flux matching premise remains. Sections 1--5
therefore prove shifted \(L^2\) for arbitrary bounded nonnormal prime transport once the
finite-to-flat expansion is available.

Thus:

```text
Hatano--Nelson exponential group:
  obstruction to direct frequency propagator only;      [CLASSIFIED]

all-orders-flat primitive flux at finite recurrence:
  exponentially weighted value and flux;                [PAPER-PROVED]

physical-root dipole / flat charge:
  forced to zero by one-sided indicial law and flatness; [CLOSED]

weighted physical derivative:
  rough prime primitive must be propagated to root.      [OPEN]             (24)
```

## 7. Remaining derivative core

Weighted \(F\) and \(Y\) do not imply weighted \(F'\) for an arbitrary \(L^2\) primitive \(G\).
Indeed `(1)` contains only \(A F=Y+G\). A high-frequency oscillatory \(G\) may lie in \(L^2\)
while its derivative does not.

Suzuki's primitive is not arbitrary:

```text
G=[R,M]F-[B,M]F.                                       (25)
```

The Gamma term is order minus one, so its derivative is controlled after `(21)`. The sole
remaining derivative obstruction is the finite-range prime term \([B,M]F\). The next theorem must
prove that its rough derivative cannot return to the two physical root rows after all
event-adapted transitions, or replace root differentiation by an exact conserved flux readout.

This is `SUZUKI-ROOT-PRIMITIVE-DERIVATIVE-PROPAGATION`. It is narrower than arbitrary nonnormal
Hardy transfer and narrower than full-vector \(H^1\).

## 8. Hostile audit

1. **No pointwise inverse of \(A\).** Localization uses its quadratic lower bound.
2. **No self-adjoint \(B\).** Equation `(10)` uses only \(\|B\|\).
3. **No hidden exponential premise.** Only sources are exponentially weighted; the state starts
   superpolynomially flat.
4. **No terminal constant deletion.** Zero flux charge follows from the first flux equation and
   superpolynomial block flatness by `(11a)`.
5. **No derivative overclaim.** Only \(F,Y,Y'\) are weighted; \(F'\) remains open.
6. **No low-frequency overclaim.** Physical dipole/flat charge is killed, but literal boundary
   counterterms still have to be assembled with the high carrier.
7. **No RH claim.** Root derivative, nonzero-trace return, raw Evans injectivity, and other Connes
   producer classes remain.

## 9. Novelty boundary

Cutoff commutators, diagonal dominance, exponential envelopes, and backward Volterra inequalities
are classical separately. Candidate-new source knowledge is the exact Suzuki chain

```text
primitive cutoff flux
 -> arbitrary-nonnormal coercive graph
 -> automatic zero-charge backward Volterra law
 -> all-orders flat implies Gamma exponential weight
 -> Hatano--Nelson group bypassed at value/flux level.  (26)
```

External priority remains unaudited.

## 10. Lean decision

The exact primitive-flux identities, scalar absorption step, exponential sequence envelopes,
infinite-tail Volterra lemma, and automatic terminal-charge squeeze are formal.  The new
declarations are `tendsto_natCast_mul_of_superpolynomiallyFlat` and
`flat_flux_terminal_charge_automatic` in
`SuzukiFlatFluxChargeAutomatic.lean`.  Full Bochner/Gamma application remains represented by the
paper bridge rather than an axiom.

## Gates

- [x] prove localized Gamma graph estimate
- [x] prove zero terminal flux charge from flatness and exact flux equation
- [x] derive backward flux tail from the automatic zero charge
- [x] prove flat Volterra exponential-upgrade lemma
- [x] prove arbitrary-nonnormal flat value/flux upgrade
- [x] formalize sequence envelope/Volterra/automatic-charge infrastructure in Lean
- [x] verify physical-root dipole and flat flux charge vanish
- [x] prove root primitive derivative propagation
- [ ] prove trace-zero completed modes enter \(H^1_0\)
- [ ] prove raw Evans injectivity or whole-Connes no-go
