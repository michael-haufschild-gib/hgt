# Prime-framed integral--nuclear homotopy defect

- **ID:** `ULF-FBG-002`
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor framed-operator theorem
- **RH used:** no
- **Divisor used:** no
- **Parents:** `ULF-FBG-001`, `ULF-PHPTCIS-001`, `ULF-PHIN-001`

## 1. What the object must be

The corpus already has a positive prime-mixed nuclear operator `T` of trace one and a signed
wall family called an integral--nuclear homotopy defect. The latter is not a homotopy across the
neutral wall: its trace jumps from `-1` to `0` to `+1`. The retired `ULF-INHD-001` also proves that
identifying a bounded source nuclear factor with the completion-born horizon is an RH-equivalent
receiver.

The missing source object is therefore not another bare trace-class operator. It is one
trace-class operator together with the singular prime-formation frame whose nuclear shadow it
regularizes. This card constructs that **framed nuclear cycle** and proves its exact topology
defect.

## 2. Construction

Let

```text
H = ell2(Nat x Primes),
T = primeHodgeHistoryIntegralNuclearDefectT.
```

Thus `T>=0`, `T` is Schatten-one, `Tr(T)=||T||_1=1`, and its matrix entry between `(n,p)` and
`(n,q)` is nonzero for every history `n` and every pair of primes `p,q`.

For `a in R`, define diagonal self-adjoint contractions

```text
V_a e_(n,p) = sech(a log(p)/2)e_(n,p),
C_a e_(n,p) = tanh(a log(p)/2)e_(n,p).                (FNH.1)
```

Put

```text
U_a = [[V_a,-C_a],[C_a,V_a]] on H direct_sum H,
W_a x = (V_a x,C_a x),
P_a = W_a W_a*,
mathcal T_a = W_a T W_a*.
                                                               (FNH.2)
```

The object nobody asked for is the single framed cycle

```text
mathfrak T = (T; a |-> W_a, P_a, mathcal T_a),        (FNH.3)
```

not any one component of `(FNH.3)` after forgetting the others.

## 3. Theorem A: exact integral--nuclear lift and recovery

For every `a`,

```text
U_a*U_a=U_a U_a*=I,
W_a*W_a=I,
mathcal T_a=U_a (T direct_sum 0) U_a*,                (FNH.4)

mathcal T_a>=0,
mathcal T_a is Schatten-one,
Tr(mathcal T_a)=||mathcal T_a||_1=1,                  (FNH.5)

W_a* mathcal T_a W_a=T.                               (FNH.6)
```

In channel blocks,

```text
mathcal T_a = [[V_a T V_a, V_a T C_a],
                [C_a T V_a, C_a T C_a]].             (FNH.7)
```

For `a!=0`, every one of the four channel blocks has nonzero entries between every two primes on
each fixed history fibre. Thus the off-diagonal blocks retain reflection orientation and the
complete same-history cross-prime coherence discarded by the two marginal traces.

**Proof.** The scalar identity `sech(x)^2+tanh(x)^2=1` and commutativity of diagonal multipliers
give `(FNH.4)`. Unitary conjugation preserves positivity and Schatten-one membership. Cyclicity
of trace and `W_a*W_a=I` give

```text
Tr(W_a T W_a*)=Tr(T W_a*W_a)=Tr(T)=1.
```

A positive trace-one operator has trace norm one, proving `(FNH.5)`. Equation `(FNH.6)` follows
by multiplying `W_a*W_a=I` on both sides of `T`. Expanding gives `(FNH.7)`. If `a!=0`, all finite
prime values of `sech(a log(p)/2)` and `tanh(a log(p)/2)` are nonzero; multiplying the already
nonzero kernel of `T` proves the last claim. QED.

Equation `(FNH.6)` is stronger than conservation of marginal traces: theta polarization lifts
the full prime-mixed state and the common recovery kernel returns it exactly. Formation is
information-neutral at this level.

## 4. Theorem B: genuine closed nuclear homotopy

The map

```text
a |-> mathcal T_a
```

is trace-norm continuous on `R`. Moreover,

```text
lim_(a->+infinity) mathcal T_a
 =lim_(a->-infinity) mathcal T_a
 =0 direct_sum T                                         (FNH.8)
```

in trace norm. It therefore extends to a closed trace-norm loop on the one-point compactification
of `R`. Reflection is the fixed gauge

```text
mathcal T_(-a)=S mathcal T_a S,
S=diag(I,-I).                                            (FNH.9)
```

**Proof.** The diagonal multipliers `V_a,C_a` and their adjoints vary strongly continuously by
pointwise continuity and dominated convergence. If uniformly bounded operators `A_j,A` and their
adjoints converge strongly and `K` is trace class, then

```text
||A_j K A_j* - A K A*||_1 ->0.                          (FNH.10)
```

Indeed approximate `K` in trace norm by a finite-rank operator; strong convergence is uniform on
its finite-dimensional source and range, while the discarded tails are uniformly bounded in
trace norm. Apply `(FNH.10)` to `A_j=W_(a_j)`.

As `a->+infinity`, uniformly over primes,

```text
||V_a||=sech(a log(2)/2)->0,
||C_a-I||=1-tanh(a log(2)/2)->0.
```

For `a->-infinity`, `C_a->-I` instead. Both signs disappear in `W_a T W_a*`, giving `(FNH.8)`.
Parity of `sech` and `tanh` gives `(FNH.9)`. QED.

This repairs the false idea that the signed trace jump itself is a continuous homotopy. The
integral unit does not cross zero; it rotates through a second channel.

## 5. Theorem C: exact strong/norm homotopy defect

The frame is strongly continuous at the neutral wall but maximally nonuniform over primes. For
every `a!=0`,

```text
||W_a-W_0||=sqrt(2),
||P_a-P_0||=1.                                          (FNH.11)
```

Nevertheless,

```text
||mathcal T_a-mathcal T_0||_1 ->0 as a->0.             (FNH.12)
```

**Proof.** On a basis vector with prime `p`,

```text
||(W_a-W_0)e_(n,p)||^2
 =(v_a(p)-1)^2+c_a(p)^2
 =2(1-v_a(p)).                                         (FNH.13)
```

For fixed `a!=0`, `v_a(p)->0` along the primes, so the supremum is `2`; this proves the first
identity in `(FNH.11)`. On each prime fibre, `P_a` and `P_0` are rank-one projections onto lines
with sine of their angle equal to `|c_a(p)|`. Hence

```text
||P_a-P_0||=sup_p |c_a(p)|=1.
```

Strong continuity follows pointwise from `(FNH.1)` and dominated convergence. Equation
`(FNH.12)` is Theorem B. QED.

Thus `mathfrak T` is exactly an **integral--nuclear homotopy defect**: its prime-formation
projection stays one full norm unit away from the neutral projection at every nonzero grade,
while multiplication by the literal prime-mixed nuclear state makes the corresponding orbit
trace-norm continuous. Closed nuclear observation erases a fixed open multiplier defect.

## 6. Theorem D: projective integer and nuclear unit are jointly carried

For every prime `p`, the compactified frame line

```text
a |-> [sech(a log(p)/2),tanh(a log(p)/2)] in RP1       (FNH.14)
```

has degree `+1`. All prime fibres therefore carry the same projective integer, while `T` couples
different prime fibres and assigns the complete cycle the nuclear unit `Tr(mathcal T_a)=1`.
Equations `(FNH.6)` and `(FNH.11)--(FNH.14)` package four facts in one object:

```text
projective degree = 1,
nuclear trace = 1,
open projection jump = 1,
closed recovery defect = 0.                            (FNH.15)
```

**Proof.** Substitution `u=a log(p)` is orientation preserving because `log(p)>0`; Theorem A of
`ULF-FBG-001` gives degree one. The remaining identities have been proved above. QED.

## 7. What this changes

The conserved anomaly is not a scalar. It is the framed package `(FNH.3)`:

- `P_a` carries the noncompact projective formation end;
- `mathcal T_a` carries its finite prime-mixed nuclear shadow;
- `W_a*mathcal T_aW_a=T` is exact information-neutral recovery;
- the difference between norm topology of `P_a` and trace-norm topology of `mathcal T_a` is the
  singular completion datum.

This explains why closed positive marginals, ordinary trace, and strong limits repeatedly become
grade-blind: each forgets the frame. It also narrows the missing completion theorem. Completion
must compare **framed cycles**, not bare operators, scalar anomalies, or projection traces.

## 8. Hostile audit and selection limit

The unframed loop `a |-> mathcal T_a` is null-homotopic in the convex space of positive
trace-one Schatten operators:

```text
(r,a) |-> (1-r)mathcal T_a+r(0 direct_sum T).           (FNH.16)
```

Therefore neither its trace nor its ordinary trace-class homotopy class selects `a=0`. Its
projective degree survives only in the frame, which is not norm-continuous at the prime-infinity
corner. This is not RH and does not evade the retired `ULF-INHD-001` bounded/singular dichotomy.

The new surviving edge is precise: construct the actual theta completion as a second framed
cycle with the same universal degree-one principal frame, form their relative mapping-cone class,
and prove its source-derived nuclear representative is bounded by the primitive Euler budget.
Any additional completed escape unit would then be an integer strictly below one. That relative
comparison is open; declaring it at Xi support would again be an RH receiver.

## 9. Formal status

Paper proof is unconditional and dependency-closed. Lean already certifies `T`, its integral
nuclearity and prime mixing, and the scalar/operator visibility--contrast laws. The coherent
two-channel orbit, trace-norm continuity, and exact norm jumps `(FNH.4)--(FNH.12)` have not been
assembled in Lean. No Lean file was written or built during this read-only research programme.
