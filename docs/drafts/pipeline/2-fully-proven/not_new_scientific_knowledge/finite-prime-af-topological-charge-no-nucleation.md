# A norm-regular finite-prime quantum universe cannot nucleate divisor charge

- **ID:** `finite-prime-af-topological-charge-no-nucleation`
- **Stage:** 2-fully-proven / finite amplification core formalized in Lean
- **Type:** THEOREM / OPERATOR-K-THEORY AND TOPOLOGICAL-PHASE NO-GO
- **Scientific status:** `[PROVED; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** independent pivot into quasi-local quantum spin systems and operator K-theory; separate
  from RHTower Routes A--D
- **Statement:** In a norm-regular AF thermodynamic limit of finite-prime matrix algebras, every
  parameterized integer winding class has a finite-stage ancestor.  If every finite cutoff has zero
  charge, the infinite quasi-local limit has zero charge.  An RH-divisor charge can therefore emerge
  only through a finite-stage zero, a gap-closing singular limit, or a non-AF/state-dependent index
  category.

## 1. Prime-indexed quantum universe

Let `P_N` be an increasing finite set of primes.  Attach a finite-dimensional local Hilbert space
`H_p` of dimension `d_p>=2` to each prime and put

```text
H_N = tensor_(p in P_N) H_p,
A_N = B(H_N) = M_(D_N)(C),
D_N = product_(p in P_N) d_p.                                 (1)
```

The inclusion obtained by adjoining a new prime is

```text
iota_N : A_N -> A_(N+1),
iota_N(a)=a tensor I_(d_(N+1)).                               (2)
```

The norm completion

```text
A=indlim_N A_N                                                 (3)
```

is a UHF, hence AF, C-star algebra.  This is the standard quasi-local observable algebra of the
prime-indexed quantum spin system.  No Hamiltonian or time flow has been added.

The unparameterized fact `K_1(A)=0` is not enough for RH: divisor winding requires a spectral
parameter.  Let `Gamma` be a positively oriented contour homeomorphic to `S^1` and define

```text
B_N=C(Gamma) tensor A_N,
B=C(Gamma) tensor A.                                          (4)
```

An invertible matrix family `U_N in GL(B_N)` has the integer determinant charge

```text
q_N=wind_Gamma(det U_N).                                      (5)
```

## 2. Finite amplification theorem

`[PROVED ON PAPER; PROVED IN LEAN]` If a new local factor has dimension `d>0`, then

```text
det(U tensor I_d)=det(U)^d,                                   (6)
q(U tensor I_d)=d q(U).                                       (7)
```

Consequently

```text
q(U tensor I_d)=0 iff q(U)=0.                                 (8)
```

Independent local enlargement can amplify an existing charge but cannot nucleate one.

### Proof

For square matrices `U` and `V`, the Kronecker determinant identity is

```text
det(U tensor V)=det(U)^(dim V) det(V)^(dim U).                 (9)
```

Take `V=I_d` to obtain `(6)`.  Winding is additive under products and hence satisfies

```text
wind(f^d)=d wind(f),                                          (10)
```

which gives `(7)`.  Since `d>0`, multiplication by `d` is injective on `Z`, proving `(8)`. QED.

## 3. AF thermodynamic no-nucleation theorem

`[PROVED]` For the system `(1)`--`(4)`,

```text
K_1(B)
  = indlim_N K_1(B_N)
  = indlim (Z --times d_(N+1)--> Z).                          (11)
```

In particular:

1. every class in `K_1(B)` is represented at a finite prime cutoff;
2. a compatible family whose finite-stage classes are all zero has zero limit class;
3. if invertible loops from finite stages converge in norm to an invertible loop `U in B`, and
   every approximating loop has zero class, then `[U]=0`.

### Proof

The circle algebra is nuclear, so tensoring `(3)` with `C(Gamma)` commutes with the inductive limit:

```text
B = indlim_N B_N.                                             (12)
```

Operator K-theory is continuous for C-star inductive limits.  Hence

```text
K_1(B)=indlim_N K_1(B_N).                                     (13)
```

Morita invariance and Bott periodicity give

```text
K_1(C(S^1) tensor M_(D_N)(C)) = K_1(C(S^1)) = Z.              (14)
```

Under `(2)`, equation `(7)` shows that the map on this copy of `Z` is multiplication by
`d_(N+1)`.  This proves `(11)`.

Every element of an algebraic direct limit has a representative at some finite stage, proving
parts 1 and 2.  For part 3, invertibility is open and `K_1` is locally constant on the invertible
group.  Norm convergence to invertible `U` eventually places the approximants in the same connected
invertible neighborhood as `U`.  Their common class is zero. QED.

The group in `(11)` is the relevant dimension group: for qubit primes it is `Z[1/2]`; for general
local dimensions it is the subgroup of `Q` obtained by inverting the successive `d_p`.  This changes
the allowed charge denominators after normalization, but not the finite-ancestor theorem.

## 4. Divisor consequence

Let `f` be a scalar holomorphic function nonzero on `Gamma`.  Its scalar unitary loop

```text
u_f=f/|f|                                                   (15)
```

defines a class in `K_1(C(Gamma) tensor A)`.  Under Bott periodicity this is

```text
[u_f]=wind_Gamma(f) [1_A] in K_0(A).                          (16)
```

The order unit `[1_A]` is nonzero.  By the argument principle, if `f` is holomorphic inside
`Gamma`, then `wind_Gamma(f)` is the total interior zero multiplicity.

Choose `Gamma` enclosing at least one Xi zero and avoiding the divisor.  Then

```text
[u_Xi] != 0.                                                  (17)
```

Every finite Euler product and finite Euler--Gamma weld is a holomorphic unit on any disc compactly
contained in `Re(s)>0`; its boundary winding is zero.  Therefore no norm-regular AF limit of such
zero-charge finite observables can equal the Xi boundary class.

This is the topological-phase form of the cofinal zero-preservation wall:

```text
finite charge 0 at every cutoff
  + norm-regular gapped thermodynamic limit
  => limit charge 0,

Xi divisor charge nonzero
  => finite-stage charge or singular gap closing is mandatory.             (18)
```

## 5. Attack: what the theorem does not exclude

The tempting stronger claim, “an AF observable algebra forbids topological order,” is false.  The
theorem concerns `K_1` classes of norm-continuous invertible families in the quasi-local observable
algebra.  It does not exclude:

1. **State and representation topology.** Infinite-volume ground states can have inequivalent GNS
   representations and superselection sectors even though the quasi-local observable algebra is AF.
2. **Gap closing.** A topological class may change when the determinant or spectral gap vanishes.
   For an RH model, proving that the source closes the gap only on the critical line is already the
   missing localization theorem.
3. **Crossed products.** Adding a clock automorphism and passing to `A rtimes Z` or `A rtimes R` can
   create new K-theory through the Pimsner--Voiculescu or Connes--Thom maps.  But the clock is then
   extra dynamical structure and must be derived from the Euler--Gamma source rather than postulated.
4. **Fredholm/corona indices.** An unbounded operator or Calkin quotient can carry an index absent
   from finite matrices.  This is a singular infinite-dimensional category, not an AF norm limit.
5. **Weaker convergence.** Strong, weak, distributional, or resolvent convergence need not preserve
   the invertible homotopy class.  Such a proposal must prove its own divisor-transfer theorem.

Thus the farthest surviving physics pivot is not a topological invariant of the regular quasi-local
observable algebra.  It must be topology of an infinite-volume state sector, a crossed-product clock,
or a Fredholm boundary anomaly.  The latter two already border familiar operator RH architectures;
the state-sector alternative is the genuinely different category, but it still needs a
source-selected sector whose charge is not inserted from Xi.

## 6. RH verdict

This theorem does not prove RH.  It excludes a broad implementation class:

```text
finite prime Hilbert spaces
  -> independent tensor enlargement
  -> norm-continuous quasi-local observable
  -> stable K-theory winding
  -> RH.                                                       (19)
```

The chain is impossible when all finite windings vanish.  Stable topological charge is not an
emergent substitute for the cofinal analytic theorem; in a regular AF limit it is precisely the
same finite-ancestor obligation in another category.

## 7. Lean surface

`formal/GaloisForLFunctions/PrimeQuasiLocalCharge.lean` proves:

- `PrimeQuasiLocalCharge.det_amplifyMatrix`;
- `PrimeQuasiLocalCharge.det_amplifyMatrix_eq_zero_iff`;
- `PrimeQuasiLocalCharge.windingNumber_amplifiedDeterminantLoop`;
- `PrimeQuasiLocalCharge.windingNumber_amplifiedDeterminantLoop_eq_zero_iff`.

The formal theorem uses the actual Kronecker determinant identity and the project's constructed
integer winding number.  It proves the non-placeholder finite charge law `(6)`--`(8)` without an
assumed K-theory interface.  The C-star inductive-limit theorem `(11)` remains on paper because
operator K-theory is not presently available in this Lean tree.

## 8. Parent and novelty boundary

- G. A. Elliott, *On the classification of inductive limits of sequences of semisimple
  finite-dimensional algebras*, Journal of Algebra 38 (1976), 29--44,
  <https://doi.org/10.1016/0021-8693(76)90242-8>, is the AF/dimension-group parent.
- M. Rordam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C-star Algebras*,
  Cambridge University Press, Chapters 6--12,
  <https://doi.org/10.1017/CBO9780511623806>, supplies continuity, `K_1`, Bott periodicity, and the
  six-term machinery.
- M. Pimsner and D. Voiculescu, *Exact sequences for K-groups and Ext-groups of certain
  cross-product C-star algebras*, Journal of Operator Theory 4 (1980), 93--118,
  <https://jot.theta.ro/jot/archive/1980-004-001/1980-004-001-005.html>, supplies the crossed-product
  escape.

The theorem is a direct operator-K-theory consequence and therefore a bridge, not new scientific
knowledge.  Its research value is the exact category exclusion: a regular quantum-spin
thermodynamic limit cannot be the missing source of divisor winding.

## Gates

- [x] parameterized, rather than unparameterized, charge category identified
- [x] finite tensor amplification law proved
- [x] AF inductive-limit no-nucleation theorem proved on paper
- [x] scalar divisor class and Xi consequence derived
- [x] false “AF forbids all topological order” overclaim excluded
- [x] singular and state-dependent escape categories classified
- [x] finite theorem formalized in Lean
- [x] parent-theory audit completed; classified as bridge
