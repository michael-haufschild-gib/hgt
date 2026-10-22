# Deninger Gamma-six shell principal ideal

- **ID:** `deninger-gamma-six-shell-principal-ideal`
- **Stage:** 3-formalized
- **Route:** L
- **Status:** `[PROVED] [FORMALIZED] [UNCONDITIONAL] [NOT RH]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/Deninger/DeningerGammaSixShellPrincipalIdeal.lean`

## Exact theorem

Number sorted Gamma-six shell coordinates from zero.  Since shells begin at depth three and

```text
sum_{j=3}^{m-1} 5*6^j = 6^m-216,
```

define

```text
d(n) = floor(log_6(n+216)),
g(n) = 6^(-d(n)).
```

Let `G_6` be diagonal multiplication by `g` on `ell^2(N)`.  Then:

1. its approximation numbers are exactly `a_n(G_6)=g(n)`;
2. `1/(n+216) <= g(n) <= 6/(n+216)`;
3. `G_6` belongs to weak Schatten `S_{1,infinity}` but not Schatten `S_1`;
4. every complete shell has exactly `5*6^m` coordinates and trace mass exactly five;
5. the literal Wold coordinate embedding `n |-> 6*n+1080` raises shell depth by one and scales
   `g` by exactly `1/6`;
6. for positive exponent `p`, the approximation numbers of `G_6^p` are exactly `g(n)^p`;
7. the concrete projective trace domain

   ```text
   D(alpha) : for every epsilon>0, G_6^(alpha+epsilon) is Schatten-1
   ```

   satisfies `D(alpha) <-> 1 <= alpha`;
8. consequently the forward and reflected edge powers satisfy

   ```text
   D(1-delta) <-> delta <= 0,
   D(1+delta) <-> 0 <= delta,
   D(1-delta) and D(1+delta) <-> delta=0.
   ```

## Proof kernel

`Nat.log` gives exact shell intervals.  Existing diagonal-operator infrastructure identifies
approximation numbers of any nonnegative antitone diagonal with its diagonal sequence.  The two
harmonic comparisons prove weak endpoint membership and exclude ordinary trace class.  Positive
powers above exponent one are dominated by shifted p-series.  If the projective domain held below
one, choosing `epsilon=1-alpha` would put `G_6` itself in Schatten-1, contradicting item 3.

## Formal audit

- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerGammaSixShellPrincipalIdeal.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixShellPrincipalIdeal`: pass.
- Key axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Module imported by `GaloisForLFunctions.RHTower` umbrella.

## Frontier boundary

This closes actual operator-ideal infrastructure for Route L's principal shell class.  It does not
yet formalize the vector-valued corrected Möbius tensor remainder, prove that the full remainder is
Schatten-1 after shell amplification, or construct the completed-Xi comparison preserving that
subobject.  Treating the diagonal principal operator alone as the full source would be invalid.
