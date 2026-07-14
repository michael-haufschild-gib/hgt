# Finite off-line Euler contour pole-order contradiction

- **ID:** `finite-offline-euler-contour-pole-order-contradiction`
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** finite-energy Suzuki reduction; Yukitaka Abe, *A remark on the Riemann zeta
  function*, Version 24 (Cambridge Open Engage, 29 May 2026)
- **Statement:** `[FALSIFIED]` Multiplying by a polynomial that vanishes at the finitely many
  hypothetical off-line zeros does not turn the Perron contour residues into simple poles. It
  raises their orders and leaves exactly the finite exponential-polynomial residue modes needed to
  cancel the reciprocal-zeta poles. The contour comparison therefore cannot prove that a finite
  off-line divisor is empty.

## Goal

Close the positive reduction in `suzuki-coupled-error-boundary-energy-attack.md`:

```text
finite critical contour-jump energy
  -> finitely many off-line zeros
  -> no off-line zeros
  -> RH.
```

The proposed second arrow uses the Dirichlet series for `1/zeta` and a Perron contour after
adjoining a polynomial whose zero set is the finite rightmost off-line divisor.

## Exact failure

Let `rho` be a zeta zero of multiplicity `m>=1`, and let `P` have a simple zero at `rho`. Then

```text
F(s)=1/(zeta(s) P(s))
```

has a pole of order `m+1` at `rho`, not a simple pole. Write its principal part as

```text
F(u)=sum_(r=1)^(m+1) c_(-r) (u-rho)^(-r)+O(1)
```

and put `H(w)=x^w/w`. The residue crossed at `w=rho-s` is

```text
Res_(w=rho-s) F(s+w) H(w)
 =sum_(k=0)^m c_(-k-1) H^(k)(rho-s)/k!.
```

Because `H^(k)(rho-s)` contains powers through `(rho-s)^(-k-1)`, this residue is meromorphic in
`s` with a pole through order `m+1`. It can and does match the order-`m+1` pole of `F(s)`.

Already for a simple zeta zero,

```text
F(u)=c_(-2)/(u-rho)^2+c_(-1)/(u-rho)+O(1)
```

and the crossed residue is

```text
c_(-2) H'(rho-s)+c_(-1) H(rho-s),
```

whose `H'` term has a double pole at `s=rho`. Treating only a scalar residue times
`x^(rho-s)/(rho-s)` discards this double-pole term and creates the apparent contradiction.

The latest cited preprint is itself marked non-peer-reviewed and states that the proof of its main
theorem is incomplete. Earlier version notes repeatedly identify serious errors in attempted
proofs of the same claim.

## Positive residue theorem

The corrected contour calculation is useful. A finite off-line divisor produces a finite sum of
exponential-polynomial anti-causal modes: a zero of multiplicity `m` contributes derivatives

```text
H^(k)(rho-s),  0<=k<m,
```

equivalently time-side modes

```text
t^k exp(-(Re(rho)-1/2)t) exp(-i Im(rho)t).
```

Thus the failed pole-order contradiction positively recovers the finite-rank contour-jump carrier
proved in `euler-leakage-residue-mode-expansion.md`. The higher principal parts are not an error
term to bound away; they are the exact coordinates of the hypothetical finite off-line divisor.

## Consequence for the RH chain

The Suzuki chain remains live through its first arrow, but the second arrow cannot be supplied by
formal pole-order bookkeeping. A successful theorem must use extra arithmetic information to
annihilate the finite residue-mode packet, for example an exact Euler-source orthogonality or
discreteness law that is not invariant under insertion of a finite symmetric polynomial divisor.

In particular, neither the functional equation, finite order, the Dirichlet series for `1/zeta` in
`Re s>1`, nor a contour shift alone distinguishes the exact zeta source from the same completed
function with a finite FE--Schwarz packet inserted.

## Gates

- [x] finite-exception contradiction isolated
- [x] pole multiplicities expanded exactly
- [x] omitted higher residue terms identified
- [x] positive finite residue-mode statement retained
- [ ] find a source-specific arithmetic law annihilating every finite nonempty residue packet
- [ ] compose that law with finite contour-jump energy and the existing Cauchy threshold

