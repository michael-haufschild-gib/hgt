# Mass-shifted first-contact curvature quotient

- **ID:** `mass-shifted-first-contact-curvature-quotient`
- **Stage:** 3-formalized
- **Type:** THEOREM / quantitative plateau classification
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- **Frozen claim:** Every first nonzero Padé contact of a positive shifted-Xi flat face—odd or
  even—canonically produces a negative source-first Hankel witness. Its exact negative energy,
  divided by actual integral Lipschitz cost, is a lower bound for displacement to one scalar
  terminal frontier. Arbitrarily long zero-contact plateaux therefore erase neither source
  amplitude nor quantitative frontier travel; they only shift degree at which price is charged.

## Exact frontier before conjecturing

`XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource` proves sharp displacement

```text
y + (-Q_y(x))/W(x) <= tau_k
```

for every negative vector in block size `k+2`, and identifies immediate odd contact with exact
determinant curvature. `XiShiftedCanonicalAdmissionEvenContactSource` proves qualitative escape
at every first even contact. `XiShiftedHankelBoundaryPadeContactParity` proves lifted-null Gram
laws at arbitrary contact order. Missing statement is quantitative and parity-complete: current
quotient only prices immediate odd contact (`m=0`), while first contact can drift arbitrarily far
along a flat Padé plateau.

## Conjecture -> proof/fail loop

1. **C1 — immediate odd remainder prices every strict frontier step. `[FALSIFIED]`** Immediate
   remainder can vanish. Corpus even-contact theorem permits a rank-filled extension after an
   arbitrarily long null flag. Adding `Delta != 0` would discard exact escape branch.
2. **C2 — a vanishing immediate remainder makes plateau quantitatively invisible. `[FALSIFIED]`**
   At first surviving contact, two lifted null descendants have zero self-energy and nonzero mixed
   energy equal to that first defect. Indefiniteness is therefore not merely existential.
3. **C3 — first surviving coupling admits one universal adaptive completion. `[PAPER-PROVED]`**
   For any real symmetric form `B`, if `B(u,u)=0`, `gamma=B(u,v)!=0`, and `a=B(v,v)`, then

   ```text
   x = u - gamma/(|a|+1) v
   B(x,x) = -gamma^2 * (2*(|a|+1)-a)/(|a|+1)^2 < 0.
   ```

   This survives both parity branches and, after exact integral Lipschitz transport, yields the
   claimed frontier quotient.
4. **C4 — parity-complete quotient alone closes RH. `[FALSIFIED]`** It supplies a positive price
   at every first contact but no degree-uniform lower bound on sum of prices. Positive survivor is
   exact renewal law: plateau length moves charge to later degree; it cannot remove charge.

## Dependency-closed paper proof

Let `B_y(A,C)=L_y(AC)` and `Q_y(A)=B_y(A,A)`. For a first contact of base flat monic polynomial
`P`, write `delta` for first surviving Padé defect.

### Algebraic adaptive completion

For vectors `u,v`, bilinearity and symmetry give

```text
Q_y(u+t v)=Q_y(u)+2t B_y(u,v)+t^2 Q_y(v).
```

Assume `Q_y(u)=0`, put `gamma=B_y(u,v)`, `a=Q_y(v)`, `d=|a|+1`, and `t=-gamma/d`. Since `d>0`,

```text
Q_y(u+t v)
 = -2 gamma^2/d + gamma^2 a/d^2
 = -gamma^2 (2d-a)/d^2.
```

Because `a<=|a|`, `2d-a >= |a|+2>0`; hence energy is strictly negative when `gamma!=0`.

### Odd first contact

If first contact order is `2m+1`, corpus lifted-null laws put

```text
u = P X^m
```

in kernel of block size `n+m+1`, and its first omitted coupling is exactly
`delta_(2n+2m+1)`. Take `v` to be next terminal coordinate, equivalently terminal padding in
block size `n+m+2`. The algebraic completion above is exactly existing odd adaptive witness with
`n` replaced by `n+m`. Its energy is explicit and negative.

### Even first contact

If first contact order is `2m`, `m>0`, put

```text
u = P X^(m-1),     v = P X^(m+1).
```

All defects below `2n+2m` vanish. Existing first-contact identities give

```text
Q_y(u)=0,
B_y(u,v)=B_y(P X^(m-1), P X^(m+1))
        =Q_y(P X^m)=delta_(2n+2m).
```

Thus same adaptive completion yields explicit negative energy in block size `n+m+2`, including
positive rank-fill branch where `P X^m` itself has positive energy.

### Sharp frontier landing

For both parities witness belongs to block size `k+2`, with `k=n+m`. Actual integral theorem gives

```text
|Q_b(x)-Q_a(x)| <= W(x)(b-a).
```

Negative energy implies `W(x)>0`. At
`b=y+(-Q_y(x))/W(x)`, energy is at most zero, so block cannot be positive definite. Definition of
terminal frontier gives

```text
y + (-Q_y(x))/W(x) <= tau_k.
```

Substitution of exact energy completes both parity formulas. No compactness, chosen eigenvector,
orientation reporter, persistence assumption, or numerical estimate enters.

## Hostile audit and novelty status

Generic adaptive completion is elementary symmetric-form algebra: `[BRIDGE]`, not scientific
novelty. Flat-extension theory describes PSD extensions and finite atomicity, including Bolotnikov
([arXiv:0812.4567](https://arxiv.org/abs/0812.4567)) and Laurent--Mourrain
([arXiv:0812.2563](https://arxiv.org/abs/0812.2563)); neither supplies shifted-Xi first-contact
source amplitudes or global integral-Lipschitz frontier displacement. Recent varying-weight Hankel
work such as Min--Wu ([arXiv:2510.06739](https://arxiv.org/abs/2510.06739)) studies recurrence and
fixed-weight asymptotics, not singular Padé-plateau renewal.

Candidate delta is parity-complete composition for literal shifted-Xi source: every first surviving
arithmetic defect has exact vector energy and scalar frontier price. Novelty remains unverified
pending independent specialist review.

## Remaining open core after theorem

Prove a cumulative lower bound on these parity-complete renewal prices along actual frontier
schedule. Immediate-remainder lower bounds are now known to be the wrong target: they miss even
and delayed odd contacts. Correct scalar is sum over first-surviving-contact certificates, with
degree jumps charged at landing degree.

## Lean certificate

- `formal/GaloisForLFunctions/RHTower/XiShiftedHankelFirstContactCurvatureQuotient.lean`
- umbrella: `formal/GaloisForLFunctions/RHTower.lean`

Capstones:

- `momentInner_xiShiftedAdaptiveNullPairPolynomial_self_eq`;
- `momentInner_xiShiftedAdaptiveNullPairPolynomial_self_neg`;
- `add_adaptiveNullPairEnergy_div_lipschitzWeight_le_terminalFrontier_sharp`;
- `add_firstOddPadeDefectAdaptiveEnergy_div_lipschitzWeight_le_terminalFrontier_sharp`;
- `add_firstEvenPadeDefectAdaptiveEnergy_div_lipschitzWeight_le_terminalFrontier_sharp`;
- `exists_sourceAdaptive_frontierCertificate_of_flatFace`.

Direct `lake env lean` and targeted module build pass. Capstone axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. No computation or unproved declaration enters.
Repository lint reaches this module through `GaloisForLFunctions.RHTower`; its nonzero exit is
entirely pre-existing umbrella debt in unrelated Bourgain, Deninger, Sieve, Suzuki,
`StrongTraceClassMultiplierLimit`, and `CriticalSchurIdealInertiaTransport` modules.
