# Von Mangoldt cyclic-reader opening-flux no-go

- **Stage:** 3 — formalized
- **Type:** universal rigidity / source-specific failed class / `SR-41` frontier reduction
- **RH used:** no
- **Computation used:** no
- **Parent:** `von-mangoldt-bivariate-marginal-trace-lock-no-go.md`

## Exact frontier changed

`SR-43` proved that ordinary coordinate partial traces cannot realize one fixed prime/Jacobi
marginal together with two consecutive `SR-40` jet marginals.  Its stated survivor allowed a
"singular, weighted/renormalized, non-trace-preserving cyclic reader."

This result kills finite full-matrix version of that survivor.  A weighted cyclic reader on a
finite full matrix source algebra is necessarily scalar ordinary trace, and therefore cannot
absorb actual positive jet-opening flux.

## Universal theorem

Let

```text
Phi : M_n(R) -> R
```

be linear and cyclic:

```text
Phi(A B)=Phi(B A)  for all A,B.
```

For any coordinate `i0`,

```text
Phi(A)=Phi(E_i0i0) Tr(A).                                  (1)
```

Proof uses matrix units only.  Cyclicity of

```text
E_(i,i0) E_(i0,i)  and  E_(i0,i) E_(i,i0)
```

makes all diagonal values equal.  For `i != j`,

```text
E_ii E_ij=E_ij,   E_ij E_ii=0,
```

so every off-diagonal matrix unit has value zero.  Linearity on standard matrix basis proves
`(1)`.  No positivity, continuity, normalization, or matrix symmetry is used.

## Actual Suzuki opening law

Let `R_(M,N)` be actual finite von-Mangoldt successor principal-relative matrix and let
`Phi_N`, `Phi_(N+1)` be cyclic readers on consecutive full jet matrix algebras.  If their
distinguished corner normalizations agree, then

```text
Phi_(N+1)(R_(M,N+2))-Phi_N(R_(M,N+1))
 =Phi_N(E_00) rho_M(2(N+1)+2).                            (2)
```

Existing source theorem proves

```text
rho_M(2(N+1)+2)>0
```

for every nonempty source aperture.  Hence positive corner normalization forces strict increase.
No such consecutive readers can assign one fixed completed-source value to both jet sections.

## Scientific verdict

- **Killed:** weighted, positively normalized, inclusion-compatible cyclic readers defined on
  every finite full matrix jet algebra.
- **Not killed:** a reader on a proper non-full source algebra; a genuinely singular cofinal
  anomaly that is not a finite-level cyclic functional; or a reader whose normalization explicitly
  carries opening flux.
- **Frontier movement:** `SR-41` can no longer invoke "non-trace-preserving cyclic reader" at
  finite full-matrix level.  Surviving object must lose full matrix domain or finite-level
  cyclicity, or expose exact flux in normalization.  This is a source-class no-go, not RH.

## Lean

- `formal/GaloisForLFunctions/HTGeometry/FiniteMatrixCyclicReaderRigidity.lean`
- `formal/GaloisForLFunctions/RHTower/VonMangoldtCyclicReaderFluxNoGo.lean`

Principal declarations:

- `matrixCyclicReader_eq_smul_trace`
- `finiteVonMangoldtSuccessor_cyclicReader_opening_eq`
- `finiteVonMangoldtSuccessor_cyclicReader_strictMono`
- `not_exists_fixedValue_inclusionCompatible_cyclicReaders_finiteVonMangoldtSuccessor`
