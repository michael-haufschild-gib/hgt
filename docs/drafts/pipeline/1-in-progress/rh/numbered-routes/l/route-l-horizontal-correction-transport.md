# Route L: original horizontal boundary and the complete reflection correction

- **ID:** RH-L-C64
- **Stage:** 1-in-progress
- **Target:** Full-source fixed Gamma/BV reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.

Previous turn is progress: C63 kernel-checked the complete native cofinal readout and the correction `(A(conj(v))-g_d(s(v))*A(v))*Xi^(k)(conj(v))` to a fixed degree. It did not identify this correction with an original horizontal boundary.

Current attack: locate the literal horizontal source boundary, retain its parameter and coefficient dependence, and test a source-derived transport/cancellation identity against C63's complete correction. No new graph coordinate or boundary counterterm may be defined to force the desired value.

## C64 attack and source-derived transport

The literal adiabatic boundary is `F(E M_a h) - E M_a(J h)`, with
`J h(t) = exp(-t) h(-t)`. Its Gamma endpoint is the surviving `n=1`
two-collar source. The existing finite Stokes theorem integrates its Euler
flux to the difference of its two parameter endpoints; the cofinal theorem
retains `Gamma(h) - MobiusCommutator(h)`. Neither theorem annihilates that
difference. C32 already proves that full Gamma/flux equality has exactly
the Poisson source range and rejects cancellation from collar fixedness.

The direct raw/Meyer identification conjecture therefore needs a literal
change of source coordinates. Put `psi_k(u)=(-i*u)^k*Phi(u)`, where `Phi`
is the existing full even theta source. For every positive native integer
depth `m`, the actual transported source is

```
h_(k,m)(t) = exp(-m*t/2) * psi_k(-m*t).
mu(n)*h_(k,m)(log(n*exp(-x/m)))
  = exp(x/2)*rawHead(k,n,m,x)                 (n>0).
```

The zero arithmetic term vanishes on both sides. Thus the complete
canonical Mobius preimage reconstructs the raw source at its original
coordinate, with `exp(x/2)` retained. For a prime anchor `p`, the same
identity applies to every `n=p+j`; the finitely many earlier terms must
be retained if using the all-integer preimage. The seed is a genuine
Schwartz function: use the existing tilt at `1/2`, multiply by the internal
jet polynomial, then compose with the nonzero real scale `-m`.

Now perform the existing collar exchange, rather than replacing it by
plain reflection. Evenness of `Phi` gives the exact source law

```
J h_(k,m)(t) = (-1)^k * exp((m-1)*t) * h_(k,m)(t).
```

This is the positive transport statement exposed by the failed bare-collar
identification. Native depth is not an index that can be dropped. The
Mellin coordinate of the rescaled seed is `s/m`; raw conjugate reflection
corresponds to `s -> m-conj(s)`. The existing linear collar exchange
instead sends the Mellin parameter to `1-s`. Its additional character and
the separate complex conjugation must be carried explicitly. This does
not prove that any fixed physical reader agrees with the cofinal reader.

The admitted native Mellin identity is

```
integral exp(m*s(v)*t) * h_(k,m)(t) dt = Xi^(k)(v)/m,
|Im(v)| < 1.
```

It follows by the actual change of variables `u=-m*t`; the absolute
Jacobian is `1/m`. Thus the proposed identification with a collar at
`s(v)` misses both its parameter scale and its mass normalization. After
complex conjugation, the native exchanged coordinate would be
`conj(v)+i*(1-1/m)`, whereas C63's raw reflection uses `conj(v)`.

The seed's membership in the stronger all-exponential Meyer source, the
transport of the full Fourier collar, and identification with the original
fixed degree-six BV reader remain separate obligations. Schwartz
admission alone is not strong Meyer admission. A new primitive defined
as minus C63's correction would not discharge any of these obligations.

## Search audit

Four partial cached whole-corpus deep searches were run directly, with
120-second budgets. All 80 returned candidate statements and all 80
source-method statements/assumptions were inspected. All returned hits
are source-only; inventory completeness is not kernel verification.

| Search artifact | Index generation | Snapshot/current | Files / Lean / declarations |
| --- | --- | --- | --- |
| `route-l-horizontal-reflection-correction-search.json` | 880920 | 880926 / 880927 | 57102 / 47473 / 735810 |
| `route-l-mellin-horizontal-primitive-method-search.json` | 880924 | 880934 / 880935 | 57105 / 47475 / 735842 |
| `route-l-raw-meyer-collar-transport-search.json` | 880977 | 880992 / 880992 | 57106 / 47476 / 735848 |
| `route-l-mobius-theta-gamma-inversion-search.json` | 880989 | 880999 / 881000 | 57107 / 47477 / 735857 |

Each inventory reported zero pending files, but tens of thousands of
compiler outcomes remained pending. No search returned a proof idea.
The first, second and fourth proposed one unverified ingredient group
each: unrelated Gamma correction/transgression carriers, unrelated
horizon Mellin transport, and gamma-contact iterates do not supply the
missing source map. The third returned no ingredient groups. Definitions
of residue annihilation and continuation/energy premises are not producers.
The relevant actual hits retain the absolute Dirichlet chamber and the
nonzero internal Xi jet, just as C61--C63 do.

Broad recent arXiv search used **reciprocity**, ordered by announcement.
[Camacho et al., 2609.11577v1](https://arxiv.org/html/2609.11577v1)
(10 September) was screened through its two-mode discussion: temporal
localization can coexist with complex eigenvalues and eventual renewed
growth. It supplies no global vanishing law; supplemental proofs were
not audited. [Xu--Zhao, 2609.11072v1](https://arxiv.org/abs/2609.11072)
(10 September) was screened at abstract level: reciprocal special zeta
values and polylogarithm expansions do not provide a global reciprocal
zeta continuation at the divisor. No paper theorem was imported into Lean.

## Validation status

The new 227-line leaf is
[`MobiusThetaNativeCollarSourceTransport.lean`](../../../../../../../formal/GaloisForLFunctions/RHTower/MobiusThetaNativeCollarSourceTransport.lean).
It imports the required raw-source leaf directly, avoiding the unnecessary
cofinal-readout import. The source definition, exact collar character,
termwise reconstruction, full tail reconstruction, canonical preimage,
absolute raw-tail and transported-tail admission, finite-prefix retention,
and admitted native Mellin identity all passed the final complete scratch
check at default limits, with no warnings (process 10232, exit 0).

Earlier scratch checks caught an exponential cast rewrite, a natural/real
logarithm cast, and a finite-prefix `+0` normalization issue. These were
fixed locally; no heartbeat or recursion limit was increased. The final
scratch was copied exactly to the leaf and wired immediately after C63 in
`RHTower.lean`. The final command
`lake build GaloisForLFunctions.RHTower.MobiusThetaNativeCollarSourceTransport`
passed (process 94493, exit 0; new leaf 77 seconds, 9488 dependency jobs).
Other listed modules were replayed dependencies; no full umbrella build
was started. Log: `/tmp/route-l-native-collar-source-build.log`.
The exact scratch/tree comparison and whitespace checks passed. Global
formal lint ran once (process 9880, exit 1): its only error is the
unrelated untracked shared-worktree module
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarJetQuadraticEinstein`
being unreachable from `RHTower`. Its header concerns a separate scalar
Einstein variation, and it was not modified here. Existing large-file
warnings remain. Log: `/tmp/route-l-native-collar-source-lint.log`.
The new native-collar module is explicitly wired at `RHTower.lean:6275`.
All owned scratch and named-build processes exited; no owned Lean process
remains. No commit or push was made. No numerical experiment or axiom-reporting command was
used. No RH closure or full-source fixed-reader agreement is claimed.
No universal ledger entry is warranted by this route-specific comparison.

Next mathematical attack: transport the actual Fourier collar of this
source into the fixed Gamma/BV domain, proving its admission and preserving
the character above, rather than treating the reconstructed inverse as an
already compatible physical boundary. Compare that resulting original
horizontal term with C63's correction on the same prime and Tate stages.
