# Horizontal entry transfers off-line charge into multiplicity charge

- **ID:** horizontal-entry-charge-transfer
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent theory:** elementary multiset algebra; horizontal multiplicity and symmetric-diagonal
  terms in the 2025--2026 pair-correlation literature; the in-tree winding/deck-charge motion API

## Statement

Let `Z_I` be the finite multiset of nontrivial zeros of a self-dual completed function whose
ordinates lie in a bounded interval `I` avoiding zeros at its endpoints. Assume that `Z_I` is
stable under

```text
rho |-> 1-conj(rho)
```

and write `m_rho` for the multiplicity of a distinct zero. For each ordinate `gamma`, put

```text
H_gamma = sum_(Im rho = gamma) m_rho.
```

Define four integer statistics

```text
N_I = sum_rho m_rho,
C_I = sum_gamma H_gamma^2,
D_I = sum_rho m_rho^2,
O_I = C_I-D_I,
M_I = D_I-N_I.
```

Then:

1. `O_I` and `M_I` are nonnegative even integers.
2. `O_I=0` if and only if every zero in `Z_I` lies on the critical line.
3. The horizontal-multiplicity excess splits exactly as

   ```text
   C_I-N_I = O_I+M_I.                                  (1)
   ```

4. When a simple reflected off-line pair collides into a double zero on the critical line,

   ```text
   (O_I,M_I) : (2,0) -> (0,2),
   C_I-N_I   : 2     -> 2.                              (2)
   ```

   More generally, if the pair collides with an existing critical-line zero of multiplicity
   `r`, the transfer is

   ```text
   (O_I,M_I) : (4r+2, r^2-r) -> (0, r^2+3r+2),         (3)
   ```

   and the sum in (1) remains fixed.

Thus ordinary horizontal multiplicity records a conserved collision charge but does not prevent
entry into the critical line. Entry converts cross-mass between distinct zeros at one ordinate
into multiplicity mass at one zero.

## Proof

At a fixed ordinate `gamma`, expand

```text
H_gamma^2
  = sum_(Im rho=gamma) m_rho^2
    + sum_(rho != rho', Im rho=Im rho'=gamma) m_rho m_rho'.
```

After summing over `gamma`, the second term is `O_I`, proving `C_I=D_I+O_I`. Also

```text
D_I-N_I = sum_rho m_rho(m_rho-1)=M_I,
```

which proves (1). Both `O_I` and `M_I` are even because their summands occur as ordered pairs:
`rho != rho'` and `rho' != rho` for `O_I`, and ordered pairs of distinct copies of the same zero
for `M_I`.

If an off-line zero `rho` is present, self-duality supplies the distinct zero
`1-conj(rho)` at the same ordinate, so `O_I>0`. Conversely, two distinct zeros at the same
ordinate cannot both be the unique critical-line point `1/2+i gamma`; hence `O_I>0` implies an
off-line zero. This proves item 2.

For a simple reflected pair, before collision `H_gamma=2`, so `C=4`, `D=2`, and `N=2`; after
collision the unique support point has multiplicity two, so `C=D=4` and `N=2`. This proves (2).
With an existing line multiplicity `r`, the pre-collision values are

```text
C=(r+2)^2,  D=r^2+2,  N=r+2,
```

and the post-collision values are

```text
C=D=(r+2)^2,  N=r+2.
```

Subtraction gives (3).

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The pair-correlation literature already distinguishes diagonal
terms from reflected symmetric-diagonal terms and introduces horizontal multiplicity. Equations
(1)--(3) are the elementary multiset algebra behind that distinction. The decomposition is useful
because it identifies the exact charge that a source theorem must control, but it is not a new
scientific result.

The formal tree already contains the more general parent mechanism that integer winding charge is
homotopy-invariant away from a boundary crossing and can change only at a singular crossing
(`ChargeMotion.lean`). Reformalizing (1)--(3) would add a wrapper around known algebra rather than
scientific content, so no Lean declaration is added for this bridge.

## Consequence for research

An entry-prevention theorem cannot be based on `C_I-N_I` alone: that statistic is unchanged by
collision. It must control `O_I` separately from `M_I`. For zeta, the required new mechanism is a
non-divisor-fed construction from the infinite Euler--Gamma source that either forces `O_I=0` or
forbids the transfer `O_I -> M_I`.
