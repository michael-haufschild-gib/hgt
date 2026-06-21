# C1 Proof Attempt: The Carrier As One Oriented 2-Form

Source: `docs/consolidated/08-conjectures-required.md` §1.

Claim status: `[CONJECTURE]`.

## Target Claim

There is one signed 2-form

```text
omega = dO wedge dphi,
O = log(1 + |zeta'/zeta|),
phi = arg(Gamma_infty + P),
P = zeta'/zeta,
```

whose strip-rectangle integral is positive for true continuation, negative for
finite-Euler/random-phase surrogates, and zero on `Re s > 1`.

## Proof Attempt

Work on a rectangle `R` in the `sigma,t` plane avoiding zeros and poles of the
chosen weld field `H = Gamma_infty + P`, so that a continuous phase branch
`phi` exists. Then

```text
d(O dphi) = dO wedge dphi + O d(dphi) = dO wedge dphi
```

on `R`, since `d(dphi)=0` for a single-valued phase branch. Therefore Stokes
gives

```text
int_R dO wedge dphi = int_boundary(R) O dphi.              (1)
```

This is the first useful reduction: the area carrier is equivalent, on
zero-free phase charts, to a boundary action. The sign problem is therefore not
an intrinsically two-dimensional mystery; it is the winding-weighted boundary
transport of the amplitude observable `O`.

The expression is also insensitive to adding a constant multiple of `2 pi` to
`phi`, since only `dphi` appears. Across a branch cut, the possible jump in
`phi` is integer-valued in units of `2 pi`, so `dphi` is unchanged away from the
cut and the cut contribution is exactly a winding/residue term. Thus any
non-integer continuous carrier must be the part of `(1)` left after subtracting
ordinary argument-principle winding.

## Weakened Theorem Proved Here

**Theorem C1-W.** On every zero-free rectangle admitting a continuous phase
branch for `H`, the proposed oriented 2-form satisfies

```text
int_R dO wedge dphi = int_boundary(R) O dphi.
```

The proof is the exterior-calculus computation above.

## Where The Full Proof Fails

The full conjecture needs strict sign separation against surrogates. Stokes
reduces the question to proving a signed boundary-action inequality:

```text
int_boundary(R) O_true dphi_true > 0,
int_boundary(R) O_fake dphi_fake < 0,
int_boundary(R) O_right dphi_right = 0.
```

No such inequality follows from the functional equation, from Euler convergence
on `Re s > 1`, or from the local pole model alone. The current data give
windowed signs, not an all-rectangle theorem.

The kill criterion is real: if an FE-exact/correct-zero fake reproduces the same
boundary action, the form is measuring FE/zero content rather than native HGT
content.

## Missing Input

1. A canonical choice of rectangles/windows independent of experimental tuning.
2. A gauge-invariant subtraction of the integer winding part.
3. A strict boundary-action inequality for true `xi`.
4. A fake-family theorem showing the inequality fails for FE-exact/correct-zero
   non-HT surrogates.
