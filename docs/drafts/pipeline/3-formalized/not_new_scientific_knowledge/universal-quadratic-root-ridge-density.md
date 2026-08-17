# Universal quadratic-root ridge density identity

- **ID:** `universal-quadratic-root-ridge-density`
- **Stage:** `3-formalized`
- **Type:** `[PAPER-PROVED] [BRIDGE] [REDISCOVERED] [POSITIVE SALVAGE]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, `(PF1)`--`(PF7)`
- **Statement:** For the reducible root packet `r(r+h)=0` modulo a nonzero modulus, the two
  universal branches `r=0` and `r=-h` each carry exactly one full Fourier ridge, the two ridge
  selectors are conjugate pointwise, and the root density is exactly one minus the
  ambient-normalized real mass of every nonzero root response.

## Exact statement

Let `n>=1`, `h in Z`, and

```text
R_(n,h)={r in Z/nZ : r(r+h)=0},
nu_h(n)=#R_(n,h),
S_(n,h)(a)=sum_(r in R_(n,h)) exp(2 pi i a r/n).
```

Then, with every frequency sum taken over `Z/nZ`, one has

```text
sum_a S_(n,h)(a)=n,                                    (UR1)

sum_a exp(2 pi i a h/n) S_(n,h)(a)=n,                 (UR2)

exp(2 pi i a h/n) S_(n,h)(a)=conj(S_(n,h)(a))         (UR3)
                                                        for every a,

if 2c=h in Z/nZ, then
Im(exp(2 pi i a c/n) S_(n,h)(a))=0                    (UR3a)
                                                        for every a,

nu_h(n)/n
 =1-(1/n)sum_(a!=0) Re S_(n,h)(a).                    (UR4)
```

Thus the untwisted full frequency sum selects the universal root `0`, while the `h`-twisted sum
selects the other universal root `-h`.  Equation `(UR4)` is an exact identity, not an estimate.

## Dependency-closed paper proof

For `x in Z/nZ`, primitivity of the standard additive character gives the finite orthogonality law

```text
sum_a exp(2 pi i a x/n)=n  if x=0,
                         =0  otherwise.               (UR5)
```

Interchanging the two finite sums in the left side of `(UR1)` and applying `(UR5)` leaves one
copy of `n` for each root equal to `0`.  There is exactly one such residue, and `0` belongs to
`R_(n,h)`, so `(UR1)` follows.

Likewise, after inserting the twist, the inner character is

```text
exp(2 pi i a(r+h)/n).
```

Orthogonality leaves one copy of `n` exactly when `r=-h`.  This residue always belongs to
`R_(n,h)` because `(-h)((-h)+h)=0`, and it is unique.  This proves `(UR2)`.

The map

```text
iota_h(r)=-h-r
```

is an involution of `R_(n,h)`: its defining product is
`(-h-r)(-r)=r(r+h)`.  Reindexing the response by this involution gives

```text
conj S_(n,h)(a)
 =sum_r exp(-2 pi i a r/n)
 =sum_r exp(2 pi i a(h+r)/n)
 =exp(2 pi i a h/n) S_(n,h)(a),
```

which is `(UR3)`.

If `c+c=h`, conjugating the centered response and applying `(UR3)` gives

```text
conj(exp(2 pi i a c/n)S(a))
 =exp(-2 pi i a c/n)exp(2 pi i a h/n)S(a)
 =exp(2 pi i a c/n)S(a).
```

It is therefore real, proving `(UR3a)`.  In particular every odd modulus admits a unique such
center because multiplication by `2` is then invertible.  The theorem only needs the exact
equation `2c=h` and is also valid in any even-modulus sector where that equation is solvable.

At frequency `a=0`, every character value is one, hence
`S_(n,h)(0)=nu_h(n)`.  Removing that term from `(UR1)` yields

```text
sum_(a!=0) S_(n,h)(a)=n-nu_h(n).
```

Taking real parts and dividing by `n>0` proves `(UR4)`.

## Hostile audit and significance

- **Merged branches:** if `h=0 mod n`, then `0=-h`; `(UR1)` and `(UR2)` select the same root.
  The proof counts residues, not named branches, so no multiplicity is fabricated.
- **Composite moduli and zero divisors:** `(UR5)` uses the primitive standard character on the
  additive group.  It does not require `n` prime or a field structure.
- **Reality:** individual responses need not be real.  Only the complete nonzero-frequency sum in
  `(UR4)` is asserted real without a phase correction.  Equation `(UR3a)` gives the exact stronger
  statement when a half-gap center exists: after one deterministic phase twist, every individual
  response is real.  It asserts no sign.
- **No cancellation estimate:** `(UR4)` fixes the signed average exactly but gives no useful bound
  for a physical subfamily of frequencies and no correlation across `h`, causal colors, or
  first-crossing sectors.
- **No AC25 smuggling:** no cutoff, source profile, Möbius weight, or endpoint estimate occurs.

The ingredients are ordinary finite Fourier orthogonality and an elementary root involution.
Accordingly the theorem is `[REDISCOVERED]` / `[BRIDGE]`, not new scientific knowledge.  Its exact
positive insight for the failed first-moment route is nevertheless substantive: **the two
reducible branch ridges are conserved selectors, while all nonzero responses have a forced real
mean `1-nu_h(n)/n`; averaging the common physical response over frequency cannot be treated as
mean-zero noise.  Moreover, wherever the gap has a half-center, the entire response packet lies on
a deterministic phase line after centering.**  Any genuine FCRJ cancellation must therefore
correlate this forced mean and real amplitude with the physical source and the global `h,p,a,r`
joining rather than estimate root responses as arbitrary complex noise in isolation.

## Gates

- [x] Exact internal audit against `(PF1)`--`(PF7)` and the reduced-frequency alias module.
- [x] Parent-theory audit: finite Fourier orthogonality; verdict `REDISCOVERED` / `BRIDGE`.
- [x] Complete dependency-closed proof `(UR5)` -> `(UR1)`--`(UR4)`.
- [x] Hostile composite-modulus, merged-root, and complex-response checks.
- [x] Exact Lean theorem and axiom gate — `GaloisForLFunctions.RHTower.UniversalQuadraticRootRidgeDensity`;
      axioms `[propext, Classical.choice, Quot.sound]`.

## Lean formalization — 2026-08-17

`formal/GaloisForLFunctions/RHTower/UniversalQuadraticRootRidgeDensity.lean` (pre-existing; verified
and audited on 2026-08-17), unconditional: `#print axioms` = `[propext, Classical.choice, Quot.sound]`
for every theorem below.

| Paper step | Lean name |
|---|---|
| the root packet `R_(n,h)` and its count `nu_h(n)` | `quadraticCongruenceRoots`, `quadraticCongruenceRootCount` |
| the response `S_(n,h)(a)` | `quadraticCongruenceZModRootResponse` |
| `(UR5)` finite additive orthogonality | `sum_stdAddChar_mul_eq_ite` |
| the universal roots `0` and `-h` | `quadraticCongruenceZeroRoot`, `quadraticCongruenceNegativeGapRoot` |
| the branch involution `r ↦ -h-r` | `quadraticCongruenceRootInvolution` |
| `(UR1)` | `sum_quadraticCongruenceZModRootResponse` |
| `(UR2)` | `sum_quadraticCongruenceZModRootResponse_twist` |
| `(UR3)` | `quadraticCongruenceZModRootResponse_twist_eq_conj` |
| `(UR3a)` | `star_stdAddChar_halfGap_mul_quadraticCongruenceZModRootResponse`, `im_stdAddChar_halfGap_mul_quadraticCongruenceZModRootResponse_eq_zero` |
| `S(0) = nu_h(n)` and the nonzero-frequency mass | `sum_ne_zero_quadraticCongruenceZModRootResponse` |
| `(UR4)` | `quadraticCongruenceRootDensity_eq_one_sub_average_re_ne_zero` |

No primality or field structure of the modulus is used, matching the card's composite-modulus audit;
the merged-branch case `h ≡ 0` needs no separate treatment because the Lean proofs count residues.

Not formalized, and not an obligation of this card: the "hostile audit and significance" discussion,
which interprets the identities for the FCRJ route rather than asserting new statements.

## Log

- 2026-08-17 Verified the pre-existing Lean module against the card statement, audited its axiom
  footprint, and promoted to stage 3.
