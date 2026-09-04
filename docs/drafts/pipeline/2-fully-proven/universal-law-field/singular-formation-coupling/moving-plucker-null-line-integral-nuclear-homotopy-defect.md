# Moving Pluecker null-line integral--nuclear homotopy defect

- **ID:** `ULF-MPNLIH-001`
- **Stage:** `2-fully-proven`
- **Type:** unconditional pre-divisor source-completion theorem
- **Parents:** `ULF-TPFOI-001`, `ULF-IFOCC-001`, `ULF-TCPSS-001`, `ULF-POSGND-001`
- **Status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH SELECTION]`
- **Lean status:** not formalized; current research stage is Lean read-only

## Big-picture interpretation

Theta completion fails to descend from the packet presentation to shared physical prime-depth
cells. The failure is not merely negative. Conjugating one-step formation by the forced singular
half-density differentiates the unbounded gauge into a bounded weighted shift. Its chiral
self-commutator is a trace-class, integer-trace boundary defect.

This constructs a new fixed-edge moving-line realization without a zero or divisor:

```text
literal Euler Pluecker formation + theta first-exit completion + physical overlap
  -> bounded completion-conjugated formation shift C
  -> T = C* C - C C*
  -> Tr(T)=1=-index(C).
```

Unlike the earlier separable defect `history tensor fixed-prime-kernel`, the fibre of this `T`
is the moving null line of the literal four-cell Pluecker block. In physical source coordinates
its prime coupling therefore changes with depth.

## Corpus audit before construction

`scripts/formal_tools.py research` was run for moving Pluecker kernels, physical overlap,
completion/quotient noncommutation, weighted-shift self-commutators, Fredholm index, and theta
relative curvature. Exact inputs are:

- `[CORPUS]` `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_ker_eq_span` identifies the
  one-dimensional nullspace of each positive rank-three physical packet.
- `[CORPUS]` `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector` is the inverse square
  root of the reciprocal-gap node. Since that node is the square of the inverse Stokes gap, its
  four coordinates are the positive Stokes gaps.
- `[CORPUS]` `gammaSewnCriticalPrimeDepthPacket_node_depth_overlap` and
  `gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_depth_overlap` identify the shared
  physical cell in consecutive packet presentations.
- `[CORPUS]` `ULF-TPFOI-001` proves that the physical Pluecker depth partition has order `-6`,
  theta first-exit has order `-4`, and their positive half-density has order `+1`.
- `[CORPUS]` `ULF-IFOCC-001` sharpens this to the successive-ratio law
  `s_(e+1)/s_e=1+1/e+O(e^-2)`.
- `[CORPUS]` `ULF-POSGND-001` proves that this gauge cannot descend pointwise through physical
  overlap.
- `[CORPUS COLLISION]` `primeHodgeHistoryRelativeCurvatureOperator_eq_selfCommutator` already
  realizes the generic theta weighted-shift trace/index law. Therefore weighted-shift index
  theory is not the novelty claim here. New residue is the source-specific conjugation by the
  Euler/theta order comparison on moving physical Pluecker null lines.

Closest external parents are weighted-shift self-commutator trace formulae and relative
index/spectral-flow theory. Parker's 2025 extension of Berger--Shaw explicitly includes weighted
shifts (<https://arxiv.org/abs/2508.02896>); Gesztesy--Latushkin--Makarov--Sukochev--Tomilov
identify Fredholm index with spectral shift in a relative trace-class setting
(<https://arxiv.org/abs/1004.1582>); Berkani proves a commutator trace formula for B-Fredholm
operators (<https://arxiv.org/abs/1609.01695>). No novelty is claimed for those abstract facts.

## Source data

Fix primes `p<q`. Let

```text
P_e = gammaSewnCriticalPrimeDepthPacket_Partition(e,p,q) > 0,
w_e = 630/((2e+3)(2e+5)(2e+7)(2e+9)) > 0.
```

`P_e` is the sum of all six literal Cauchy--Binet minor weights of the four-cell packet

```text
(p,e), (p,e+1), (q,e), (q,e+1).
```

No global normalization is needed. Put

```text
g_e = sqrt(w_e/P_e),
a_e = (g_e/g_(e+1))^2
    = w_e P_(e+1)/(w_(e+1) P_e),
alpha_e = sqrt(a_e)>0.                                 (MPNLIH.1)
```

This is exactly the forced completion connection of `ULF-TPFOI-001`: there
`pi_e=F_pq P_e/Z_pq`, with `F_pq,Z_pq` independent of depth, so

```text
g_e=sqrt(F_pq/Z_pq) s_e,
g_e/g_(e+1)=s_e/s_(e+1).
```

The global depth normalizer cancels before `C_pq` is formed.

Let `I_r>0` be the critical Stokes inverse tilt of prime `r`. The canonical packet-null vector is

```text
v_e=((e+1)I_p,(e+2)I_p,(e+1)I_q,(e+2)I_q) in C^4,    (MPNLIH.2)
u_e=v_e/||v_e||,
L_e=C u_e.
```

Let

```text
K_pq = directSum_(e>=0) L_e
```

with canonical orthonormal basis `epsilon_e`, where `epsilon_e` is supported at depth `e` with
value `u_e`. Define the bare formation shift `V epsilon_e=epsilon_(e+1)`, the unbounded
half-density `G epsilon_e=g_e epsilon_e`, and

```text
C_pq epsilon_e=alpha_e epsilon_(e+1).                  (MPNLIH.3)
```

On the finite-history core this is exactly

```text
C_pq=G^-1 V G.                                         (MPNLIH.4)
```

Thus `C_pq` is forced by completion before physical-overlap quotient; it is not a fitted weighted
shift.

## Theorem MPNLIH

For every fixed prime edge `p<q`:

1. `C_pq` extends to a bounded Fredholm operator on `K_pq`, is injective, has range
   `epsilon_0^perp`, and

   ```text
   index(C_pq)=-1.                                     (MPNLIH.5)
   ```

2. The self-adjoint homotopy defect

   ```text
   T_pq=C_pq* C_pq-C_pq C_pq*                         (MPNLIH.6)
   ```

   is nuclear and has diagonal form

   ```text
   T_pq epsilon_0=a_0 epsilon_0,
   T_pq epsilon_e=(a_e-a_(e-1))epsilon_e,  e>=1.       (MPNLIH.7)
   ```

3. If `Q_N` projects onto histories `0,...,N`, then the exact finite-boundary law is

   ```text
   Tr(Q_N T_pq Q_N)=a_N,                               (MPNLIH.8)
   ```

   and consequently

   ```text
   Tr(T_pq)=1=-index(C_pq).                            (MPNLIH.9)
   ```

4. In the literal embedding `K_pq subset ell2(N,C^4)`, `T_pq` has depth block

   ```text
   a_0 |u_0><u_0|                         at e=0,
   (a_e-a_(e-1)) |u_e><u_e|              at e>=1.      (MPNLIH.10)
   ```

   Its zeroth block has every cross-prime matrix entry nonzero. Hence `T_pq` is prime-mixed.

5. Relative to the literal prime-depth coordinate algebra, `T_pq` is not
   `diagonal-history tensor fixed-packet-operator`. It is therefore genuinely prime--history
   nonseparable in the source representation.

6. There is `E_pq` such that

   ```text
   a_e-a_(e-1)>0  for every e>=E_pq.                  (MPNLIH.10a)
   ```

   Hence every negative spectral direction of `T_pq` lies in a finite history head. Global
   positivity is not asserted.

Taking the first edge `(p,q)=(2,3)` gives one distinguished fixed-edge realization

```text
T := T_(2,3).                                           (MPNLIH.11)
```

## Proof

The `ULF-TPFOI-001` asymptotic for the unnormalized partition is

```text
P_e=K_pq e^-6(1+O(e^-1)),  K_pq>0,
```

and its rational-in-depth proof gives the sharper consecutive ratio

```text
P_(e+1)/P_e=1-6/e+O(e^-2).                            (1)
```

Theta telescoping gives exactly

```text
w_(e+1)/w_e=(2e+3)/(2e+11)=1-4/e+O(e^-2).            (2)
```

Using `(MPNLIH.1)`, `(1)`, and the reciprocal of `(2)` gives

```text
a_e=1-2/e+O(e^-2).                                    (3)
```

In particular `a_e->1`. Positivity and a positive limit imply

```text
0<inf_e a_e<=sup_e a_e<infinity.
```

Thus `C_pq` is bounded and bounded below. It is injective. Its range is exactly the closed
codimension-one tail because every target coefficient can be divided by the corresponding
`alpha_e`, uniformly. This proves `(MPNLIH.5)`.

The adjoint satisfies

```text
C_pq* epsilon_0=0,
C_pq* epsilon_(e+1)=alpha_e epsilon_e.
```

Substitution proves `(MPNLIH.7)`. Equation `(3)` also gives

```text
|a_e-a_(e-1)|=O(e^-2).
```

Indeed subtract the two expansions; the principal difference is
`2/(e(e-1))`, while both remainders are `O(e^-2)`. Therefore

```text
|a_0|+sum_(e>=1)|a_e-a_(e-1)|<infinity,
```

so `(MPNLIH.7)` defines a self-adjoint Schatten-one operator. Finite traces telescope:

```text
a_0+sum_(e=1)^N(a_e-a_(e-1))=a_N.
```

Taking `N->infinity` and using `a_N->1` proves `(MPNLIH.8-9)`.

Every raw minor in `P_e` is rational in the real depth variable, and the finite sum, theta
weight, shifts, products, and quotients in `(MPNLIH.1)` preserve rationality near infinity.
Therefore `(3)` has a one-order sharper Laurent expansion

```text
a_e=1-2/e+c_pq/e^2+O(e^-3)
```

for some real `c_pq`. Subtracting its shift gives

```text
a_e-a_(e-1)=2/e^2+O(e^-3)>0
```

eventually. This proves `(MPNLIH.10a)`.

For prime mixing, every coordinate of `u_0` is strictly positive by `(MPNLIH.2)`, and `a_0>0`.
Therefore every matrix entry of `a_0|u_0><u_0|`, including all four entries joining a `p` cell
to a `q` cell, is nonzero.

For nonseparability, the ratio of the second and first coordinates of `v_e` is

```text
(e+2)/(e+1),
```

so `L_e != L_f` whenever `e!=f`. Equation `(3)` implies the sequence `a_e` is not eventually
constant; hence `(a_e-a_(e-1))` is nonzero for infinitely many `e`. If `(MPNLIH.10)` were a
history diagonal tensored with one fixed nonzero packet operator, all its nonzero rank-one blocks
would have the same range. The zeroth block and any later nonzero block instead have distinct
ranges `L_0` and `L_e`. Contradiction.

Finally, on `K_pq directSum K_pq`, let

```text
D_pq=[[0,C_pq*],[C_pq,0]].
```

Its two chiral Laplacians are `C_pq* C_pq` and `C_pq C_pq*`. Each is non-nuclear because its
diagonal tends to one, while their difference is exactly the nuclear operator `(MPNLIH.6)`. This
is the precise sense in which `T` is a homotopy defect rather than a decorative name. QED.

## Exact conservation and reconstruction

The same unit now has five source-side readings:

```text
half of (Pluecker tail order 6 - theta tail order 4)
  = formation logarithmic residue
  = limit of finite homotopy boundaries a_N
  = -Fredholm index(C_pq)
  = nuclear trace(T_pq)
  = 1.                                                  (MPNLIH.12)
```

Moreover `T_pq` reconstructs every transport square by cumulative block trace:

```text
a_N=Tr(Q_N T_pq Q_N),
g_(N+1)/g_0=product_(e=0)^N a_e^(-1/2).                (MPNLIH.13)
```

Thus nuclear boundary data reconstructs the singular completion gauge up to its irrelevant
initial scalar. This is dynamic information absent from a static trace-one tensor product.

## Hostile review

**Wrong first.** A unilateral weighted shift, its Fredholm index, and telescoping trace of its
self-commutator are classical. Abstractly `K_pq` can be trivialized to `ell2(N)`, so this theorem
does not create a new operator-theory species.

**Why it is not the old object.** The permissible equivalences are source-faithful: they must
respect literal prime-depth coordinates and physical overlap. In that representation the lines
`L_e` move, the zeroth block mixes both primes, and `ULF-POSGND-001` forbids the pointwise physical
gauge that would trivialize the completion before quotient. The new content is this exact
source-generated realization, not the generic weighted-shift normal form.

**Coefficient-completeness attack.** `T_pq` retains the full six-minor partition and the canonical
moving kernel line, but not the whole rank-three covariance block. It is source-owned and
prime-mixed, not yet a complete reconstruction of every unsquared Euler coefficient. Any Xi
comparison must either prove that the null-line/index sector is sufficient or lift this defect to
the full Pluecker quotient without losing `(MPNLIH.9)`.

**Circularity attack.** `P_e`, `w_e`, `v_e`, `g_e`, `C_pq`, and `T_pq` are defined before any Xi
zero or divisor is supplied. No horizontal grade or RH-equivalent landing occurs.

**Sub-unit attack.** Since `Tr(T_pq)=1`, necessarily `||T_pq||_1>=1`. This object cannot be the
missing `<1` source budget and does not revive retired `ULF-INHD-001`. Its role is the universal
integral anomaly to be subtracted before a residual estimate.

**Positivity attack.** The proof establishes self-adjointness and trace class, not
`T_pq>=0`; global monotonicity of `a_e` has not been proved. No positivity conclusion may be used
without a separate source theorem.

**Corpus-collision correction.** The corpus already contains the genuinely global object named
`primeHodgeHistoryIntegralNuclearHomotopyDefect`, with every prime mixed in every history fibre,
first-exit reconstruction, trace one, and a Fredholm colligation.  Thus `(MPNLIH.11)` is not the
requested global object and choosing `(2,3)` is not source-canonical.  Its only surviving content
is the different physical realization: completion conjugation on a moving Pluecker null line.

**Verdict.** Dependency-closed unconditional fixed-edge realization. Novelty is unverified. It
narrows physical-overlap behavior but does not supersede the existing global defect and is not
selection.

## Exact RH-chain edge

Any viable relative-completion theorem must now compare the completed Xi boundary with
`T_pq` as the already-paid unit anomaly, not try to manufacture an integer from the sub-unit
Euler budget. The exact surviving edge is:

```text
literal completion on formation presentation
  -> universal source defect T_pq with Tr=1
  -> prove completed boundary = T_pq + R_pq
  -> prove R_pq is theta-positive and Tr(R_pq)=0 from source completion
  -> R_pq=0
  -> identify only the neutral horizontal grade as admissible.
```

The missing theorem is therefore a source-derived base-change identity plus residual positivity.
Merely defining `R_pq` as the difference, or assuming its positivity, is exactly the old receiver
and does not count.
