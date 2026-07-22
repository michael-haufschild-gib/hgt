# Sonin aperture Ward-curvature transgression

- **ID:** `sonin-aperture-ward-curvature-transgression`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL THEOREM / SUZUKI FRONTIER REDUCTION
- **Status:** unconditional paper proof; Lean formalization complete in companion Stage-3 card
- **Terminal status:** not RH, not not-RH, not a full Suzuki no-go

## Theorem

Let `Q_a` be the orthogonal projection onto the even Sonin carrier at aperture `a`, let

```text
L_(a,b)=Q_a-Q_b,
D_r=U_r+U_r^*,
Z_(a,b,c;r)=L_(a,b) D_r L_(b,c)
```

for `0<a<b<c<r a` and `r>1`.  Let `Delta_(a,b;r)` be the exact positive aperture-restriction
defect and

```text
Kappa_(a,b,c;r)=Delta_(a,c;r)-Delta_(a,b;r)-Delta_(b,c;r).
```

Then:

1. successive aperture layers are orthogonal;
2. `Z_(a,b,c;r)` is Hilbert--Schmidt;
3. the curvature trace is the exact negative boundary energy

   ```text
   Re Tr Kappa_(a,b,c;r)=-||Z_(a,b,c;r)||_HS^2;
   ```

4. trace is faithful on this curvature:

   ```text
   Re Tr Kappa=0 iff Kappa=0 iff Z=0;
   ```

5. for the canonical self-adjoint Ward channel `X=Z+Z^*`,

   ```text
   2 Re Tr Kappa+||[X,L_(a,b)]||_HS^2=0.
   ```

The last identity is an exact transgression law: one half of the canonical Ward commutator energy
is the unique positive square which cancels the scalar aperture curvature.

## Proof

The exact compressed cocycle gives

```text
Kappa=Q_c Delta_(a,b;r) Q_c-Delta_(a,b;r).
```

The first defect is a Gram operator `Delta=Y^*Y`, where
`Y=L_(a,b)D_rQ_b`.  General trace-class compression geometry gives

```text
Tr(Q_cY^*YQ_c-Y^*Y)
 =-Tr((1-Q_c)Y^*Y(1-Q_c)).
```

The complementary Gram is `Z^*Z`, since nesting gives

```text
Y(1-Q_c)=L_(a,b)D_r(Q_b-Q_c)=Z.
```

Trace-class membership of `Z^*Z` implies `Z` is Hilbert--Schmidt, and the ordinary trace of
`Z^*Z` is `||Z||_HS^2`.  This proves the energy identity.  Positivity makes trace faithful:
zero trace forces `Z=0`, and then `Y=YQ_c`, hence `Q_cY^*YQ_c=Y^*Y` and `Kappa=0`.

Finally `L_(a,b)L_(b,c)=L_(b,c)L_(a,b)=0`.  With `X=Z+Z^*`, the lower boundary of `X` across
`L_(a,b)` is exactly `Z^*`.  The two-corner commutator identity gives

```text
||[X,L_(a,b)]||_HS^2=2||Z||_HS^2,
```

which yields the transgression law.

## Suzuki verdict impact

This closes the aperture-curvature experiment in the terminal ledger.  Curvature is neither an
unknown signed anomaly nor a possible independent source of coercivity.  It is a fixed negative
square with a canonical Ward cancellation.

The corpus Burnol edge is a bounded, generally noncompact conductor commutator, whereas `Z` is the
Hilbert--Schmidt relative remainder after principal aperture mass has been removed.  Therefore the
remaining source theorem is precise: prove that the **relative finite part** of Suzuki's concrete
Burnol conductor supplies exactly one half of this Ward energy.  A literal equality of the raw
conductor edge with `Z` is the wrong operator-class statement.

Even exact cancellation does not prove the completed prime--Gamma lower floor.  After aperture
transgression, the RH-bearing problem is still the canonical co-Poisson/Burnol source sign.  No
terminal verdict is claimed.

