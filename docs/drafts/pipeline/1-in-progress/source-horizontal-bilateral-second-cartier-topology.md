# Source-horizontal bilateral second-Cartier topology

- **ID:** `P-G211-BSCT`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE LOOP] [SOURCE-TOPOLOGY PRODUCER]`
- **Route:** Frankenstein P + integral Cartier/Big-Witt + bilateral Hardy--Stokes + Gamma/Ward
- **Statement:** Replace scalar first-conormal admission by the minimal second infinitesimal
  source neighborhood which retains odd Hardy orientation and even inversion curvature as
  independent coordinates.

## Exact problem

The prior endpoint-annihilation theorem constructs exact signed cancellation, but ordinary
bilateral moderation rejects every strict off-line Xi copy. Scalar rescaling cannot change that.
The source must therefore admit the two Hardy chambers before scalar moderation without erasing
their coefficient or the nonlinear inversion defect.

Let

```text
R = Z[q,q^-1],       g = q-1,       I = (g),       sigma(q)=q^-1.
```

The first conormal `I/I^2` is too small: it forces `[sigma(g)]=-[g]`. The proposed carrier is the
second infinitesimal source neighborhood `I/I^3`. Its three canonical classes are

```text
F = [g],       R = [sigma(g)],       G = [g^2].
```

Here `F` and `R` are the two Hardy orientations and `G` is the even Gamma/Ward curvature ghost.

## Frozen conjecture loop

### C0 -- quadratic inversion survives minimally

In `I/I^3`, prove

```text
F + R = G,
sigma(F)=R,
sigma(R)=F,
sigma(G)=G,
G != 0.
```

Moreover `F,R` are integrally independent. Thus the carrier is genuinely rank two. Passing to
`I/I^2` kills exactly `G` and is the scalar collapse already proved in the corpus.

### C1 -- coefficient-faithful Hardy descent

For `lambda != 0`, define

```text
Phi_lambda(a,b) = a h_+(lambda) + b h_-(lambda).
```

Prove `Phi_lambda` injective by the source coordinates `e=0` and `e=-1`. Then

```text
Phi_lambda(F)=h_+(lambda),
Phi_lambda(R)=h_-(lambda),
Phi_lambda(G)=h_+(lambda)+h_-(lambda)=h_bilateral(lambda),
D_lambda Phi_lambda(G)=0.
```

The range with its transported two-dimensional topology is the required non-scalar source
topology. It admits both Hardy orientations simultaneously for every nonzero character, while
retaining their separate coefficients.

### C2 -- endpoint and Xi fidelity

Multiply `Phi_lambda` by the literal nonzero Euler--Wold endpoint energy. Prove injectivity is
preserved, both source orientations retain the actual Gamma--Julia conormal coefficient, and fibre
summation restores `xiSupportMultiplicity` on each orientation and on `G`.

### C3 -- hostile boundary

This construction must not be advertised as RH. Off line, the rank-two source topology exists but
its three physical sequences fail ordinary fixed-circle moderation. Prove

```text
Phi_lambda(G) is moderate  <->  |lambda|=1,
both Phi_lambda(F), Phi_lambda(R) are moderate  <->  |lambda|=1.
```

Hence second-Cartier descent genuinely solves simultaneous source admission, but relocates the RH
burden to a source-derived physical order/budget law on the nonzero even ghost `G`. Any quotient
that kills `G` returns the scalar `I/I^2` firewall.

## Hostile audit

- Enhanced moderate/rapid nearby cycles place growing and decaying sectors in dual chambers for
  arbitrary exponential rate; sectorial duality alone does not force neutral grade.
- The full Laurent source already carries both orientations, but without finite source topology it
  does not explain which nonlinear datum must survive. `I/I^3` is the first quotient retaining the
  exact inversion curvature.
- A modular positive receiver fits each prime by changing the inverse coefficient. The present
  carrier forbids that: `F`, `R`, and `G=F+R` are fixed source classes before prime evaluation.
- Killing `G` by an additive reporter is already RH-equivalent. The producer here retains `G`; it
  does not assume its physical annihilation.

## Literature boundary

Augmentation-ideal quotients and their associated graded rings are classical. Enhanced
ind-sheaves provide moderate/rapid sectorial duality, and semilocal Hardy/Sonin theory provides
two-channel operator carriers. No located primary source identifies the second Laurent
augmentation neighborhood with the Xi-selected bilateral Hardy pair and the exact Gamma/Ward
curvature ghost. Novelty of this cross-corpus identification remains to be audited after proof.

## Gates

- [x] 0 -> 1: exact source-pure conjectures frozen
- [ ] C0 algebraic second-neighborhood proof
- [ ] C1 injective bilateral Hardy descent
- [ ] C2 endpoint/Xi coefficient and multiplicity fidelity
- [ ] C3 sharp moderation firewall
- [ ] dependency-closed paper proof
- [ ] unconditional Lean leaf and axiom audit
- [ ] umbrella wiring without umbrella build

## Log

- 2026-08-18 -- Scalar and sectorial-duality candidates rejected; second Cartier neighborhood
  selected because it retains the exact quadratic inversion ghost as an independent source leg.
