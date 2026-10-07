# Two-prime projective real packets

- **ID:** RH-TPRP-20261006
- **Stage:** 3-formalized
- **Type:** classical bridge / exact receiver re-expression; source producer OPEN
- **Parent:** `../1-in-progress/xi-legendre-integral-cylinder-comparison.md`;
  `../1-in-progress/rh-nonmetric-infinite-geometry-loop.md`
- **Goal:** replace a prescribed half-density metric or a fixed real involution by existence of
  a projective real form on two finite arithmetic marking packets. No RH conclusion is assumed.

## Exact statement

For `s in C`, put `a_p(s)=exp((1/2-s) log p)`, for `p=2,3`. A packet is the labelled four-tuple
`(1,a_p,a_p²,a_p³)`. Say a packet lies on a generalized circle if there exist real `A,D` and
complex `B`, with `B conjugate(B) != A D`, such that

```
A z conjugate(z) + B z + conjugate(B) conjugate(z) + D = 0
```

at its four entries. The determinant condition excludes point conics, and the marked point
`1` ensures that the equation has a solution.
Repeated markings are allowed; no cross-ratio denominator is
discarded. The two packets may have different circle equations.

This is a projective real-form condition: the equation is the fixed locus of
`[z0:z1] -> [-conjugate(B) conjugate(z0)-D conjugate(z1) :
A conjugate(z0)+B conjugate(z1)]`. Its anti-linear matrix squares to the nonzero real
scalar `B conjugate(B)-A D`, hence defines an anti-holomorphic projective involution.
The point `[1:1]` is fixed, excluding the fixed-point-free real form. This projective
interpretation is proved on paper; Lean below formalizes the equivalent explicit equation.

**Classification:** both packets admit such an equation iff `Re s=1/2` or `Im s=0`.
Consequently at nonreal Xi/zeta divisor points this is a finite projective-real RH receiver.
The exact source character is the existing `deningerKummerCharacter (1/2-s)` on rational
scaling basis elements. It is not a newly fitted character.
This is a character of the full Kummer group ring; no descent through the positive
Steinberg square quotient, or geometric realization of its Hochschild class, is asserted.

## Dependency-closed paper proof

First let `a!=0`. Suppose a circle equation vanishes on `a^n`, `n=0,1,2,3`.
Its four exponential bases are `a conjugate(a), a, conjugate(a), 1`; its coefficients are
`A,B,conjugate(B),D`. If `a` is nonreal and `a conjugate(a)!=1`, these bases are pairwise
distinct. Equality of either middle base with the product or with one would force `a` real
or zero. The Vandermonde matrix is therefore invertible, forcing all coefficients zero,
a contradiction. Thus `a=conjugate(a)` or `a conjugate(a)=1`.

Conversely a real `a` uses the real-line equation (`A=D=0`, `B=i`), and a unit-modulus `a`
uses `A=1,B=0,D=-1`. Both coefficient matrices have determinant `-1`.
This proves the single-packet classification, including every collision. The same classification
holds for merely nonzero equations: the forward proof uses only their nontriviality.

For `a_p=exp((1/2-s)log p)`, the product with its conjugate is
`exp(2(1/2-Re s)log p)`. Since `log p!=0`, it equals one iff `Re s=1/2`.
Away from that line, both packets therefore force their respective `a_p` to be real.
An exponential is real iff its imaginary exponent belongs to `pi Z`; hence
`Im s log 2 = k pi`, `Im s log 3 = l pi` for integers `k,l` (signs may be absorbed).
If `Im s!=0`, then `k!=0` and `log 3/log 2=l/k`, contradicting the already formalized
irrationality of the two-prime log ratio. Thus `Im s=0`. The converse follows from the
real-line and unit-circle equations already exhibited.

No estimate, infinite-prime limit, positive form, or numerical experiment occurs in the proof.

The Lean proof uses the already formalized integer independence `two_prime_log_indep`
directly: multiply the two phase identities crosswise, cancel nonzero `pi`, and obtain
`l log 2 - k log 3=0`. Thus `k=l=0`. No transcendence theorem is needed.

The source comparison is required at every power: `a_p(s)^k` is the image under the existing
Kummer character of the `k`th power of the rational-scaling basis element. The actual
nonreal-zero restriction is discharged by the existing real-strip zeta nonvanishing theorem;
the global Xi correspondence then gives an exact equivalence with mathlib's RH statement.
This equivalence does not prove its packet-real side.

## Geometric construction to test

Before selecting a zero, form the source graphs

```
w = -a_p(s)^k xi(s),    p=2,3, k=0,1,2,3,
```

in the same marked blowup of `(w,xi(s))` used by the proper-family programme. Their strict
transforms meet an exceptional component at `-a_p(rho)^k`, preserving the terminal multiplicity
jet. Multiplication by `-1` does not change generalized-circle existence. Only seven distinct
labels are needed because the two `k=0` sections agree. Equivalently, choose the fixed blowup
coordinate `t=-w/xi` before selecting any zero; its marks are exactly `a_p(rho)^k`.
The proposal is to obtain a real form
fixing each packet from the completed source, not to impose unit modulus on its coordinates.

**OPEN CORE:** construct those componentwise real forms from the original source. Functional
equation symmetry exchanges components over `rho` and `1-conjugate(rho)`; it does not by itself
fix either component. Existence of the required real forms at every divisor point remains
RH-bearing. Neither the blowup nor the classification supplies it.

The current proper-family source section is recorded separately in
`../1-in-progress/xi-legendre-formal-source-section.md`. Its exact global two-division covers
and non-torsion statement do not remove this gap: the division tower splits locally at the
Xi degeneration, and global non-divisibility can disappear after a meromorphic pullback.
The next source comparison must retain this distinction.

## Hostile and novelty audit

The attempted shortcut "functional equation plus source markings supplies componentwise
real descent" fails. For any nonreal `rho` off the critical line, the exact polynomial

```
F_rho(s)=(s-rho)(s-conjugate(rho))(s-(1-rho))(s-(1-conjugate(rho)))
```

has real coefficients and satisfies `F_rho(1-s)=F_rho(s)`. The same simultaneous graph and
blowup construction exists for `F_rho`, but its packet at `rho` fails the classification.
On the exceptional projective lines, `s -> 1-conjugate(s)` transports the marks by
`t -> 1/conjugate(t)`; it need not fix their component. This is an exact symbolic
countermodel to the proposed symmetry-only inference, not a counterexample to Xi or RH.
The positive survivor is the complete two-prime classifier proved above. The missing
producer must use more of the actual Xi arithmetic source than these symmetries.

The existing `DeningerDivisorGaugeWardIdentity.lean` already proves a nonmetric
anti-linear-gauge receiver: commuting with the divisor generator plus one nonzero cup
diagonal forces the critical line. Its explicit reflection gauge has diagonal one, but its
commutation defect is precisely `1-rho-conjugate(rho)`. Thus the new packet criterion does
not remove an existing source premise. A real coefficient system on cohomology also does
not by itself give a geometric real form fixing all labelled marks.

Corpus audit: the two packet searches and subsequent componentwise-descent deep search
returned `partial:false` with complete inventory snapshots; compiler metadata still had
pending/stale entries and semantic coverage was unmeasured. The deep search's proposed
fiber-product/vector-bundle ingredient set supplies no real-descent theorem from the Xi
source and was rejected on its stated signatures and unresolved obligations.

- **Verdict: BRIDGE.** Generalized-circle reality and Vandermonde rigidity are classical.
  No significant scientific novelty is claimed for the classification. It is a finite,
  coordinate-independent re-expression of an existing geometric receiver.
- In contrast to assuming a prescribed unit circle, arbitrary circle/line equations are
  permitted separately for the two prime packets. Their possible split-real branch is retained
  and removed only by the actual nonreal-divisor fact.
- Repeated powers and negative real characters are not exceptions to be excluded.
- Three generic marks always admit a circle; fourth powers supply the load-bearing test.
- Internal searches: `prime character cross ratio real circle`, `four powers character circle
  Vandermonde`, exhaustive focused `concyclic`/`real form` source search. Reciprocal-character
  real-form mechanics is an existing parent; its positive-energy admission is not used here.
- Primary classical reference: [Sertoz, Complex Analysis II solutions, Q3](https://sertoz.bilkent.edu.tr/courses/math302/2013/mid1-sol.pdf)
  proves the generalized-circle/real-cross-ratio criterion. The present proof uses a homogeneous
  equation to retain collisions rather than divide by cross-ratio denominators.
- Earlier relative-Kummer-period proposal was audited against
  [Dupont–Fresan, §2.1](https://arxiv.org/html/2305.00789v2): it has a classical geometric model
  and does not supply the missing source-fixed real structure. No duplicate Lean leaf was added.

## Formal implementation and verification

- `HTGeometry/FourPowerGeneralizedCircle.lean`: nonsingular Hermitian equation and exact
  real/unit classification, including all marking collisions; 83 lines.
- `RHTower/XiTwoPrimeProjectiveRealPackets.lean`: full Kummer-source comparison for every
  power, integral phase classification, two-prime classification, zeta/Xi zero receivers,
  and the exact RH equivalence; 160 lines.
- Both targeted `lake --old build +<module>` runs passed. The source build replayed existing
  dependency warnings in `HTGeometry/StokesCoronaSchurVanishing.lean`; no new-leaf warning.
- Both modules are wired once into their theorem-area umbrellas; indexes regenerated.
- Final direct `lake env lean` checks of both actual source files passed with empty logs.
  All 16 public declarations were audited in a separate `/tmp` file: each depends only on
  `propext`, `Classical.choice`, and `Quot.sound`. The guarded sequential audit exited zero.
- `scripts/formal_tools.py lint --check-generated` failed outside these leaves: nine unwired
  modules (`WeilConeBoundaryDilationInequality`, `WeilZetaSquareAveraging`,
  `WeilZetaSquareBoundaryInequality`, `WeilZetaSquareMoments`, `ApertureConeCalculus`,
  `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
  `BoundaryCoronaCStarAlgebra`) and an active `sorry` at line 292 of the concurrently edited
  `RHTower/WeilConeBoundaryDilationInequality.lean`. No issue names either new leaf.
  This is a snapshot of concurrent work, not a green repository gate.

Audit logs use `/tmp/rh-four-power-circle-*-20261006.log` and
`/tmp/rh-two-prime-circle-*-20261006.log`. The all-public audit contains 16 declarations.
Five obsolete scratch/check files were removed; final audit artifacts remain. No new
admission, axiom, heartbeat change, numerical research computation, or commit was used.

## Checklist

- [x] Exact classification and dependency-closed paper proof.
- [x] Source graph construction specified; missing real descent kept explicit.
- [x] Corpus applicability/API audit; formalize exact source classification.
- [x] Targeted builds, final direct-source checks, all-public axioms, and umbrella wiring.
- [x] Run global lint and record its unrelated failures without claiming a green gate.
- [x] Audit the symmetry-only descent shortcut; preserve the OPEN CORE and full RH goal.
- [ ] Construct the actual Xi-source real forms or a stronger arithmetic replacement.
