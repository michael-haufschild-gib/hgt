# FZZ-P: Fermi coupling integration and exchange

Status: paper proof and Lean audit closed, 2026-09-11. RH and the full source-framed Ward producer remain open.

## Chain and hard obstacle

Fixed theta/FZZ source → framed mixed replica–momentum Ward identity → vacuum-delay saturation → passivity → RH. The marked radial insertion is now integrated and audited, but its effective coupling depends on fields omitted from that radial calculation. The next step must evaluate a remaining coupling integral rather than assume that the radial mixed sign survives integration.

## Conjecture loop and original integrals

Use the already proved positive unit-mass logarithmic exponential density `B(u)=exp(u−exp(u))`, and the prior radial density `w(u,v,x)=b exp(u+b*x) exp(−exp(u+b*x))`, `b=exp(v)`.

A. Conjecture: this coupling integration realizes the Fermi source and its derivative exactly:

`∫ B(u) exp(−exp(u+b*x)) du = 1/(1+exp(b*x))`,

`∫ B(u) w(u,v,x) du = b exp(b*x)/(1+exp(b*x))²`.

This is a positive original double integral. The identity is with Fermi occupancy as a function of `b*x`; it does not identify the full-line Fourier variable with the original positive-delay Mellin variable of the Xi divisor.

B. Conjecture: integrating each factor before forming the reflected pair preserves the previous radial mixed-response zero set. With `q=p/b`, the integrated unmarked characteristic should be `N(p)=Gamma(1+iq)Gamma(1−iq)`, strictly positive. The integrated marked operator should have normalized response `c[digamma(1−iq)−digamma(1+iq)]`, `c=k/(k−2)`, which is purely imaginary. Pairing these separately integrated factors cancels the response and its momentum derivative for every momentum. This tests independent coupling integrations; it is not a counterexample to integrating the original pair with one shared coupling variable.

C. Positive survivor: evaluate the unpaired insertion, retain its strict orientation, prove the Fermi/logistic source representation and exact exchange law. The extra coupling moment is a source integral that precisely compensates the prior paired radial derivative; it is not an arbitrarily assigned quotient or counterterm. No claim is made that B is the physical nonzero-mode distribution of the sine-Liouville theory. Its exact source identification is the missing test for transferring the mechanism to that theory.

D. Pivot: retain the shared coupling variable of the original pair. At zero replica deficit the paired integrand is `Gamma(1+iq)Gamma(1−iq)`, independent of `u`. Its integrated marked response should therefore be `2c[Re digamma(1)−Re digamma(1+iq)]`. This has the previous strict mixed derivative and zero set `p=0`. The shared and independent source contractions must be distinguished before transferring either result to a physical correlator. These are integrated first-order operator insertions; no interchange of the outer coupling integral with a derivative of an entire finite-deficit family is assumed.

## Exact proof and positive survivor

Put `q=p/b`, `c=(2+b²)/b²`, and `z±=1±iq`. The change of variable `t=exp(u)` in the coupling integral gives the Fermi kernel. Differentiating that exact integral gives the scaled logistic density. Their joint density `B(u) w(u,v,x)` is positive, integrable and has mass one; absolute integrability justifies the Fourier Fubini identity.

The original radial characteristic and marked insertion are

`C(u,p)=exp(−iqu) Gamma(z+)`,

`D(u,p)=c[u−digamma(z+)] C(u,p)`.

The coupling characteristic and logarithmic moment are respectively `Gamma(z−)` and `Gamma(z−) digamma(z−)`. The latter follows from the previously proved original marked integral and its derivative interchange at unit coupling and slope. Thus the coupling integrals, evaluated before dividing, are

`N(p)=∫ B(u) C(u,p) du=Gamma(z+) Gamma(z−)=|Gamma(z+)|²>0`,

`I(p)=∫ B(u) D(u,p) du=c[digamma(z−)−digamma(z+)] N(p)`.

Conjugation makes `I/N` purely imaginary. The positive vertical digamma formula gives its strictly negative imaginary part for `p>0`, and reflection gives the exact zero set `p=0`. For two separately integrated factors, `I(p)N(−p)+N(p)I(−p)=0` at every momentum. Its normalized response and momentum derivative vanish identically. Conjecture B fails for that assembly.

For the shared-coupling assembly, the undeformed original product `M(u,p,0)M(u,−p,0)` equals `N(p)` before coupling integration. Its actual derivative is `2c[u−Re digamma(z+)]N(p)`. The integral of `u B(u)` is `Re digamma(1)`, so normalization after integration gives

`R_shared(p)=2c[Re digamma(1)−Re digamma(z+)]`.

Its mixed derivative is `(2c/b) Im trigamma(z+)`, strictly negative for `p>0` and zero exactly at `p=0`. At every positive momentum this derivative differs from the independently integrated paired derivative. This is the positive survivor of B: integration with a shared source variable retains the strict receiver in this explicit model. Neither result imposes its vanishing on a theta-source occurrence.

The shared source exposes a stronger first-insertion statement. Its response is zero at `p=0`; the mean-value theorem and the strict derivative sign make its real part strictly decreasing on `[0,infinity)`. Momentum reflection makes the response even. Consequently its first insertion response itself vanishes exactly at `p=0`, and is strictly negative at every nonzero momentum. This new conjecture was returned to the paper proof and checked in `/tmp/fzzp_shared_stationarity.lean` before being added to the module. It supplies a sharper receiver, not an enforcement law.

Both assemblies are diagnostic products of radial factors; neither has been identified with the complete physical winding correlator. In particular, sharing `u` does not identify the two radial integrations with one physical zero-mode integral. The paper's excluded reflected wave and the compact winding sum remain separate source-prescription issues.

## Work plan

- [x] Prove the two coupling integrals and their convergence in Lean scratch.
- [x] Prove the characteristic, integrated insertion, and exact independently paired cancellation, with every interchange used justified.
- [x] Prove the unpaired orientation and the shared-coupling mixed zero set; distinguish the missing physical-source identification.
- [x] Leaf build, all-public axiom audit, lint, umbrella import, frontier and universal-ledger updates.

## Formal audit

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarFermiCouplingExchange.lean`, 46 public theorems. Public statements have no proof-hypothesis binders; positive parameters use exponentials. Every integral interchange used in these statements has its convergence proof. The outer coupling derivative of a finite-deficit family is not asserted.

- `lake env lean /tmp/fzzp_fermi_exchange.lean`: passed for the original 42-theorem block.
- `lake env lean /tmp/fzzp_shared_stationarity.lean`: passed for the four stronger first-response theorems against the audited block.
- Final `lake build GaloisForLFunctions.RHTower.FZZCigarFermiCouplingExchange`: passed, 85 seconds, only this leaf compiled; 9105 total jobs including cached/replayed dependencies. No umbrella build.
- `lake env lean /tmp/fzzp_fermi_exchange_axioms.lean`: all 46 public theorems checked; only `propext`, `Classical.choice`, `Quot.sound`. No added axioms.
- `scripts/formal_tools.py lint`: passed, with existing large-file warnings.
- Import added to `formal/GaloisForLFunctions/RHTower.lean`; FZZ-P frontier and route-independent ledger updated.

Audit logs: `/tmp/fzzp-fermi-exchange-build.log`, `/tmp/fzzp-fermi-exchange-axioms.log`, `/tmp/fzzp-fermi-exchange-lint.log`. Scratch logs: `/tmp/fzzp-fermi-exchange-scratch.log`, `/tmp/fzzp-shared-stationarity-scratch.log`. The informational `ring_nf` suggestion in the original scratch/build output is inherited from `ExplicitDigammaHerglotzPalette`, not a failed proof in this module.

## Current-source search

Deep/method retrieval `/tmp/fzzp-source-coupling-covariance-deep.json` returned partial pending coverage (generation 823093). Inspected hits included covariance definitions and unrelated coupling matrices; none supplies the physical FZZ nonzero-mode law. Method query `/tmp/fzzp-fermi-mixture-methods.json` returned partial pending coverage at generation 823097. Exact corpus reads identified `Gamma_vertical_eq_fourier`, the previous integrated marked insertion, and the Suzuki logistic kernel and moment formulas. The shared-coupling deep/method search `/tmp/fzzp-shared-coupling-methods.json` returned partial pending coverage at generation 823132: product integration and Fourier-shift candidates were relevant infrastructure, but its proposed ingredient set did not identify the physical source law. All candidates and method-source names were inspected; proposed applicability was not treated as a theorem.

The follow-up hybrid search `/tmp/fzzp-fermi-mellin-marked-search.json` returned partial coverage at generation 823139, with 344 pending/stale source files and many pending compiler snapshots. Its Mellin/log-moment and real-slice variance hits differentiate the spectral parameter, not the original Fermi kernel. No closed source-derivative Mellin identity was returned.

## Next hard attack: retain the actual Mellin label

The proved Fourier characteristic `N` never vanishes; it is not the Xi-divisor Mellin transform. At unit slope, the coupling-integrated radial marked density is formally `−3 t exp(t)/(1+exp(t))²`. The next concrete conjecture is its Mellin identity `−3s fzzCigarParityMellin(s)` on `Re s>0`, from integration by parts against the proved derivative of the Fermi kernel. This requires the original marked-kernel identity, convergence and both boundary limits in Lean. If proved, first marked Mellin vanishing would follow at every original divisor zero and would supply no wall selection by itself. The mixed Mellin derivative, its source frame, and the actual compact/nonzero-mode contribution would then have to supply the missing orientation. This conjecture is not included in the audited theorem claims below.

Broad arXiv terms were `screening`, `transport`, and `susceptibility`, with June–September 2026 filters. [Mohammed–Robertson–Gomes, 2606.08693v1, June 7](https://arxiv.org/html/2606.08693v1), §2, uses a susceptibility density and an exact Gamma-family reduction. This suggested testing an explicit continuous coupling law; the proof here uses symbolic source integrals, not that paper's numerical results. [Seibold–Lütz–Brown, 2608.16342v1, August 17](https://arxiv.org/html/2608.16342v1) concerns graph-based energy-network planning; no applicable analytic Ward mechanism was identified.

[Halder–Jafferis, 2402.00932v3](https://arxiv.org/html/2402.00932v3), (3.14), (3.26), and (3.29)–(3.33), fixes the winding potential and marked charge and leaves a remaining position correlator after radial integration. Its torus area insertion is not evaluated. No positive exponential law for its effective nonzero-mode coupling is established in these formulas.
