# Suzuki finite-aperture boundary-phase locking

- **ID:** `suzuki-finite-aperture-boundary-phase-locking`
- **Stage:** 5 — ineligible under the hypothesis-free/Lean-complete paper gate
- **Type:** UNIVERSAL OPERATOR LIMIT LAW / SUZUKI 2026 CENTRAL CONJECTURE
- **Scientific status:** `[UNIVERSAL PART PAPER-PROVED] [RH-CONDITIONAL APPLICATION REJECTED]`
  `[NOT LEAN-COMPLETE] [NOT PUBLICATION-ELIGIBLE] [NOT RH]`
- **Primary source target:** Suzuki 2026, Sections 7.5--7.6
- **Computation used:** no

## 0. Gate verdict (2026-07-22)

This card is not eligible for the requested paper.  The abstract nested-operator law is
unconditional as an implication, but the advertised Suzuki specialization imports RH to obtain
the positive global Weil Hilbert space and target self-adjoint translation generator.  Moreover,
the full unbounded-operator theorem has not been formalized in Lean.  Neither defect may be hidden
inside a theorem statement or discharged by citation under the current gate.

The manuscript is retained only as a rejected research draft.  Current unconditional Suzuki
frontier is the later `SUZUKI-APEX-BLOCK-TRANSPORT` / restricted-Weil Robin producer recorded in
`docs/handover/sota-suzuki.md`, Sections S66--S68.

## 1. Major problem solved

Suzuki constructs, for every finite aperture `a`, a closed symmetric first-order operator with
deficiency indices `(1,1)` and a circle of self-adjoint extensions `D_(a,theta)`.  Under RH he also
constructs the global Hilbert--Polya translation generator `D`, whose spectrum is the set of Xi zero
ordinates.  He explicitly expects that one can choose `theta=theta(a)` so that

```text
D_(a,theta(a)) -> D
```

in strong resolvent sense as `a->infinity`, but gives neither an existence proof nor a phase
classification.

There is also an object-type problem: finite and global operators act in different Hilbert spaces,
so ordinary strong resolvent convergence is not literally defined.  The theorem below supplies the
correct generalized strong resolvent statement, constructs a canonical phase schedule, and
classifies every schedule that has the desired limit.

Applied to Suzuki's exact source, it proves his central finite-aperture spectral-limit conjecture
**under RH**.  This is not an RH proof: positivity of the global Weil Hilbert space and existence of
the target self-adjoint Hilbert--Polya generator are themselves downstream of RH.

## 2. Universal nested-exhaustion setup

Let `H` be a complex Hilbert space.  Let `(H_a)_(a>0)` be increasing closed subspaces with
orthogonal projections `P_a` satisfying

```text
P_a -> I strongly as a->infinity.                        (2.1)
```

Let `S_a` be closed densely defined symmetric operators on `H_a`, and let `S` be a closed densely
defined symmetric operator on `H`.  Assume

```text
S_a subset S_b subset S                 (a<b),            (2.2)
closure(union_a graph(S_a))=graph(S),                      (2.3)
def(S_a)=def(S)=(k,k),  1<=k<infinity.                    (2.4)
```

For each sign define the closed ranges

```text
M_(a,+)=range(S_a+i),      M_(a,-)=range(S_a-i),          (2.5)
M_+=range(S+i),            M_-=range(S-i),                (2.6)
```

and the deficiency spaces, using orthogonal complements in the appropriate Hilbert spaces,

```text
N_(a,+)=H_a orthogonal-minus M_(a,+),
N_(a,-)=H_a orthogonal-minus M_(a,-),                     (2.7)
N_+=H orthogonal-minus M_+,
N_-=H orthogonal-minus M_-.                               (2.8)
```

Thus `N_(a,+)=ker(S_a^*-i)`, `N_(a,-)=ker(S_a^*+i)`, and similarly globally.

## 3. Automatic deficiency-space convergence `[PROVED]`

### Theorem 3.1

Let `Q_(a,+/-)` and `Q_+/-` be the orthogonal projections onto the corresponding range spaces in
`(2.5)--(2.6)`, embedded in `H`.  Let `E_(a,+/-)` and `E_+/-` be the projections onto the
deficiency spaces.  Then

```text
Q_(a,+) -> Q_+,      Q_(a,-) -> Q_-,                     (3.1)
E_(a,+) -> E_+,      E_(a,-) -> E_-                      (3.2)
```

strongly.  Since all deficiency spaces have the same finite dimension `k`, the convergence in
`(3.2)` is in fact operator-norm convergence.

For all sufficiently large `a`, the polar decompositions of

```text
E_(a,+)|N_+ : N_+ -> N_(a,+),
E_(a,-)|N_- : N_- -> N_(a,-)                             (3.3)
```

give canonical unitaries

```text
J_(a,+):N_+ -> N_(a,+),
J_(a,-):N_- -> N_(a,-)                                  (3.4)
```

which converge in norm to the inclusions of `N_+` and `N_-` into `H`.

### Proof

For a closed symmetric operator `T`,

```text
||(T +/- i)x||^2=||Tx||^2+||x||^2,                       (3.5)
```

so `range(T +/- i)` is closed.  By `(2.2)`, the spaces `M_(a,+)` are increasing and contained in
`M_+`; likewise for the minus sign.  Given `(S+i)x in M_+`, graph exhaustion `(2.3)` supplies
`x_a in dom(S_a)` with `x_a->x` and `S_a x_a->Sx`.  Hence

```text
(S_a+i)x_a -> (S+i)x.                                    (3.6)
```

Therefore `closure(union_a M_(a,+))=M_+`.  Monotone convergence of orthogonal projections proves
the plus case of `(3.1)`; the minus case is identical.

Because `M_(a,+) subset H_a`,

```text
E_(a,+)=P_a-Q_(a,+),       E_+=I-Q_+.                    (3.7)
```

Equations `(2.1)` and `(3.1)` prove `(3.2)`.  Strong convergence of projections of constant finite
rank to a projection of the same rank upgrades to norm convergence.  Equivalently, on finite
dimensional `N_+`, `E_(a,+)|N_+` converges uniformly to the identity.  It is therefore injective
for large `a`; equality of dimensions makes it onto `N_(a,+)`.  Its polar factor is the unitary
`J_(a,+)` and converges to the inclusion.  Repeat for the minus sign.  QED.

## 4. Universal boundary-phase locking and classification `[PROVED]`

For a self-adjoint extension `A` of `S`, define its Cayley transform

```text
C_A=(A-i)(A+i)^(-1).                                     (4.1)
```

Let `V:M_+->M_-` be the partial Cayley isometry of `S`,

```text
V((S+i)x)=(S-i)x.                                        (4.2)
```

Then `C_A` is the orthogonal sum of `V` and a unitary boundary block

```text
W:N_+ -> N_-.                                            (4.3)
```

The same notation with subscript `a` is used for `S_a` and its self-adjoint extensions.

### Theorem 4.1 (existence)

Define the locked finite boundary block by

```text
W_a=J_(a,-) W J_(a,+)^*.                                 (4.4)
```

Let `A_a` be the self-adjoint extension of `S_a` whose Cayley boundary block is `W_a`.  If
`I_a:H_a->H` is the inclusion, then

```text
I_a (A_a+i)^(-1) P_a -> (A+i)^(-1)                       (4.5)
```

strongly.  Thus every global self-adjoint extension is the generalized strong resolvent limit of a
canonically phase-locked family of finite self-adjoint extensions.

### Proof

Let `V_a:M_(a,+)->M_(a,-)` be the finite partial Cayley map.  Since `S_a subset S`,

```text
V_a=V|M_(a,+).                                           (4.6)
```

Consequently the embedded finite Cayley transform is

```text
I_a C_(A_a) P_a = V Q_(a,+) + W_a E_(a,+).               (4.7)
```

The first term converges strongly to `VQ_+` by `(3.1)` and `(4.6)`.  The second converges strongly
to `WE_+` by `(3.2)--(3.4)` and `(4.4)`.  Hence

```text
I_a C_(A_a) P_a -> VQ_+ + WE_+ = C_A                     (4.8)
```

strongly.  The Cayley resolvent identity is

```text
(A+i)^(-1)=(1/(2i))(I-C_A),                              (4.9)
```

and on `H_a` it gives

```text
I_a(A_a+i)^(-1)P_a
 =(1/(2i))(P_a-I_a C_(A_a)P_a).                          (4.10)
```

Now `(2.1)` and `(4.8)` imply `(4.5)`.  QED.

### Theorem 4.2 (classification and rigidity)

Let `B_a` be arbitrary self-adjoint extensions of `S_a`, with Cayley boundary blocks
`Z_a:N_(a,+)->N_(a,-)`.  Then

```text
I_a(B_a+i)^(-1)P_a -> (A+i)^(-1) strongly               (4.11)
```

if and only if

```text
J_(a,-)^* Z_a J_(a,+) -> W in operator norm.             (4.12)
```

Thus the only asymptotic freedom is the finite-dimensional boundary unitary.  At deficiency
`(1,1)`, choose unit vectors `e_+ in N_+`, `e_- in N_-` and write

```text
W e_+=zeta e_-,
Z_a J_(a,+)e_+=zeta_a J_(a,-)e_-,    |zeta|=|zeta_a|=1.  (4.13)
```

Then `(4.11)` is equivalent to the scalar phase lock

```text
zeta_a -> zeta.                                          (4.14)
```

### Proof

If `(4.12)` holds, the proof of Theorem 4.1 applies with `Z_a` in place of `W_a`.

Conversely, `(4.11)`, `(2.1)`, and the resolvent identity `(4.9)` imply strong convergence of the
embedded Cayley transforms.  Their base parts `VQ_(a,+)` already converge strongly by Theorem 3.1,
so the embedded boundary blocks `Z_a E_(a,+)` converge strongly to `WE_+`.  Test this convergence
on `J_(a,+)x->x`, for `x in N_+`, and apply `J_(a,-)^*`.  This gives pointwise convergence in the
finite-dimensional space `N_+`; uniform boundedness and finite dimension upgrade it to norm
convergence `(4.12)`.  At `k=1`, a unitary is one unit scalar, giving `(4.13)--(4.14)`.  QED.

## 5. Spectral approximation consequence `[PROVED]`

### Theorem 5.1

Under `(4.5)`, let `lambda` be an isolated spectral point of `A`.  Every open interval `U`
containing `lambda` and no boundary point in `spectrum(A)` meets `spectrum(A_a)` for all
sufficiently large `a`.  In particular,

```text
lambda in limitinf_(a->infinity) spectrum(A_a).           (5.1)
```

### Proof

Generalized strong resolvent convergence implies strong convergence of bounded continuous
functional calculus through `P_a` and `I_a`.  Choose a nonnegative continuous function `f`
supported in `U` with `f(lambda)=1`.  Since `f(A) != 0`, strong convergence forces `f(A_a) != 0`
for all sufficiently large `a`.  Hence `spectrum(A_a)` meets `U`.  QED.

This is spectral inclusion, not norm-resolvent convergence.  The theorem does not exclude additional
finite-aperture spectral pollution away from the target spectrum.

## 6. Suzuki source verification `[PROVED FROM RH]`

Assume RH and use Suzuki's notation.

### 6.1 Hilbert-space exhaustion

Suzuki defines `H(A_a)` as the completion of `C_c^infinity(-a,a)` in the restricted Weil-form norm
and `H(A_infinity)` as the global completion/quotient.  The norm is the same global Weil form on
every compactly supported test function.  Therefore extension by zero gives isometric embeddings

```text
H(A_a) subset H(A_b) subset H(A_infinity)   (a<b).        (6.1)
```

Each image is closed because it is the isometric image of a complete space.  The union contains
all of `C_c^infinity(R)`, which is dense in `H(A_infinity)`.  Hence the orthogonal projections
`P_a` converge strongly to the identity.

### 6.2 Symmetric-operator exhaustion

On `H(A_a)`, Suzuki's minimal derivative has test domain `C_c^infinity(-a,a)` and action `i d/dx`.
Let `S_a` be its closure.  Let `S` be the closure of the same derivative on
`C_c^infinity(R) subset H(A_infinity)`.  Extension by zero and equality of the Weil norms give

```text
S_a subset S_b subset S.                                 (6.2)
```

Every global compactly supported test function lies in some finite domain.  Since that test domain
is a core by definition of `S`, the finite graphs exhaust `graph(S)`.

Suzuki proves that every `S_a` has deficiency indices `(1,1)`.  Under RH his global de Branges
model identifies `S` with the symmetric multiplication operator and gives the same indices `(1,1)`.
Thus all hypotheses `(2.1)--(2.4)` hold.

### 6.3 Target extension and phase schedule

Suzuki's global translation generator

```text
D=D_(pi/2)                                                (6.3)
```

is a self-adjoint extension of `S`, unitarily equivalent to the de Branges multiplication
extension whose spectrum is the set `Gamma` of Xi zero ordinates.  Apply Theorem 4.1 to its boundary
block `W`.  Since Suzuki parametrizes every finite self-adjoint extension by
`theta in [0,2pi)`, the locked block `(4.4)` determines a phase `theta(a)` for every sufficiently
large aperture.  It satisfies

```text
I_a (D_(a,theta(a))+i)^(-1) P_a -> (D+i)^(-1) strongly.  (6.4)
```

This is the rigorous varying-Hilbert-space form of Suzuki's expected strong resolvent limit.
Theorem 4.2 classifies all other phase schedules producing the same limit: their canonically
transported effective boundary phases must converge to the global phase.

### 6.4 Approximation of Xi ordinates

Suzuki proves that the zeros of his entire function `W(a,theta;z)` are precisely the eigenvalues of
`D_(a,theta)` and are all real.  The global target has discrete spectrum `Gamma`.  Theorem 5.1
therefore gives, for every Xi ordinate `gamma` and every `epsilon>0`,

```text
exists A  forall a>=A,
  exists x in R,
    W(a,theta(a);x)=0 and |x-gamma|<epsilon.              (6.5)
```

Thus every Xi ordinate is approximated by finite-aperture real characteristic zeros.  This proves
the spectral approximation expected in Suzuki 2026 without asserting impossible locally uniform
entire convergence to the meromorphic function `z^2 xi/xi'`.

## 7. Significance and exact boundary

### Solved

1. Universal existence of phase-locked self-adjoint extensions on any stable finite-deficiency
   nested exhaustion.
2. Necessary-and-sufficient classification of every convergent boundary schedule.
3. Correct generalized strong resolvent formulation for Suzuki's varying Hilbert spaces.
4. Suzuki's 2026 finite-aperture spectral-limit conjecture under RH.
5. Approximation of every Xi ordinate by real finite-aperture characteristic zeros.

### Not solved

1. RH is not proved; global positive Weil space and target generator use RH.
2. No explicit arithmetic closed formula for `theta(a)` is claimed.  The phase is canonical in
   operator geometry through deficiency projections and polar transport.
3. Strong resolvent convergence does not imply norm-resolvent convergence or absence of spectral
   pollution.
4. No locally uniform convergence of a single entire characteristic function to `z^2 xi/xi'` is
   claimed; the latter is meromorphic and the corpus already records this wall.

## 8. Hostile audit

1. **Different Hilbert spaces:** handled by `(4.5)`, not ordinary resolvent notation.
2. **Closed ranges:** follows exactly from `(3.5)`.
3. **Nested closures:** finite closure sequences embed with identical graph norms.
4. **Global graph core:** union of finite test domains is the global test domain.
5. **Cayley sign:** theorem uses the Cayley boundary block itself, avoiding a convention-dependent
   sign in von Neumann's `U:N_+->N_-` parametrization.
6. **Rank loss:** excluded by stable finite deficiency dimension `(2.4)`; this is load-bearing.
7. **Converse:** recovered from resolvent-to-Cayley convergence after subtracting automatic base
   convergence.
8. **Spectral claim:** only target spectral inclusion is asserted.
9. **No hidden RH:** universal theorem is unconditional; RH appears explicitly only in the Suzuki
   global-space instantiation.
10. **No computation:** proof is exact operator theory.

Verdict: `SURVIVES HOSTILE ATTACK`.

## 9. Novelty audit

- Bjerg 2023 proves, on one fixed Hilbert space, precise implications between convergence of given
  deficiency-space partial isometries and strong resolvent convergence of their extensions.
- Teschl--Wang--Xie--Zhou 2026 systematize generalized strong/norm resolvent convergence for varying
  Hilbert spaces and its spectral consequences.
- Neither inspected source states automatic convergence of deficiency projections for a nested
  graph exhaustion, constructs the canonical polar phase transport `(3.3)--(4.4)`, or applies the
  result to Suzuki's Weil-form aperture chain.
- Suzuki 2026 states the phase-selection/strong-resolvent limit as an expectation and does not cite
  or prove such an exhaustion theorem.
- Internal corpus has extensive finite-aperture phase, Cayley, and meromorphic-limit analysis but no
  theorem constructing a generalized-strong-resolvent phase schedule.

Universal operator ingredients are adjacent to existing extension theory.  Candidate novelty is
the automatic nested-exhaustion phase-locking theorem, its converse classification in varying
spaces, and resolution of Suzuki's stated spectral-limit conjecture.  Independent priority review
is still required.

## 10. Gates

- [x] central Suzuki 2026 open conjecture identified
- [x] correct varying-space convergence notion
- [x] dependency-closed universal proof
- [x] source-exact Suzuki hypothesis verification
- [x] adjacent-literature comparison
- [ ] manuscript completed
- [ ] exact Lean formalization
- [ ] independent specialist novelty review
