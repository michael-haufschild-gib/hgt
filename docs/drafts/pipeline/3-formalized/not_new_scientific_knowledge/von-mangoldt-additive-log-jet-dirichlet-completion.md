# Von Mangoldt additive log-jet Dirichlet completion

- **ID:** `von-mangoldt-additive-log-jet-dirichlet-completion`
- **Stage:** 3-formalized
- **Type:** `[SOURCE-SPECIFIC POSITIVITY]`, `[OFF-DIAGONAL COMPLETION]`, `[BRIDGE]`
- **Scientific status:** `[PROVED LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/VonMangoldtAdditiveLogJetDirichlet.lean`.
- **Parents:**
  `../../1-in-progress/prime-gamma-reflection-decimation-defect-resolvent-rh.md`.
- **Statement:** The integral successor incidence with conductance `Lambda(n)/n` sends every
  logarithmic Mellin jet to an `ell^2` vector, and its complete finite jet tower is a positive
  Hilbert Gram tower.

## Exact source theorem

Let

```text
f_r(n)=(log n)^r,
d f_r(n)=f_r(n+1)-f_r(n),
c(n)=Lambda(n)/n,
v_r(n)=sqrt(c(n)) d f_r(n).                              (1)
```

Lean proves the discrete mean-value estimate

```text
|d f_r(n)| <= r (log(n+1))^(r-1)/n                      (2)
```

for `n>=1`, and the source majorant

```text
c(n)|d f_r(n)|^2
 <= 8 r^2 |log(n+1)|^(2r-1) (n+1)^(-3)                 (3)
```

for `r>=1`, `n>=2`.  Consequently

```text
sum_n c(n)|d f_r(n)|^2 < infinity                       (4)
```

for every `r`, including the constant jet.  Each `v_r` is therefore an actual vector in
`ell^2(N,R)`.  The mixed products `sum_n v_r(n)v_s(n)` are absolutely summable, and

```text
G_N(r,s)=<v_r,v_s>,  0<=r,s<N                           (5)
```

is positive semidefinite for every `N`.  Its diagonal is exactly the total Dirichlet energy in
`(4)`.

## What this changes

The resolved-prime diagonal positive-log energy diverges at every logarithmic order.  Applying
the integral successor derivative before the norm supplies an unconditional off-diagonal repair:
the associated operator is the weighted graph Laplacian `d^* C_Lambda d`, not a scalar or
coefficientwise reweighting.  Positivity is obtained from the actual von Mangoldt source before
any Xi zero or target moment measure is read.

This is not yet an RH source producer.  Additive successor incidence does not visibly preserve
Euler multiplication, and no theorem identifies `(5)` with the normalized prime--archimedean
Hankel matrix.  In fact Lean proves that direct identification is impossible at every nonempty
size: the successor derivative kills the constant jet, so `(5)` has a zero zeroth row, while the
normalized prime--archimedean Hankel matrix has strictly positive `(0,0)` entry.  A pointed
boundary completion is therefore logically necessary and must supply a nontrivial boundary jet,
not merely rename the edge Gram.  The exact discriminator is a Gamma/polar Green--Schur identity
derived from the completed source boundary:

```text
Schur_Gamma,polar(d^* C_Lambda d)(r,s)
 = normalizedPrimeArchMoment(r+s).                      (6)
```

Proving `(6)` for every finite section would transport `(5)` to the already formalized complete
prime--Gamma Hankel cone and hence to RH.  Failure of Euler compatibility kills this route; the
positive Gram alone is only a carrier.

## Lean certificate

The module proves:

- `log_natCast_succ_sub_log_natCast_le_inv`;
- `abs_vonMangoldtAdditiveLogJetDifference_le`;
- `vonMangoldtAdditiveLogJetEnergy_le_majorant`;
- `summable_vonMangoldtAdditiveLogJetEnergy`;
- `vonMangoldtAdditiveLogJetFeature_sq`;
- `memℓp_two_vonMangoldtAdditiveLogJetFeature`;
- `summable_vonMangoldtAdditiveLogJetFeature_mul`;
- `vonMangoldtAdditiveLogJetGram_posSemidef`;
- `vonMangoldtAdditiveLogJetGram_apply`;
- `vonMangoldtAdditiveLogJetGram_diagonal`.
- `vonMangoldtAdditiveLogJetGram_zero_row`;
- `vonMangoldtAdditiveLogJetGram_ne_primeArchSourceMomentHankelMatrix`.

The construction module and its companion
`formal/GaloisForLFunctions/RHTower/VonMangoldtAdditiveLogJetPointedNoGo.lean` are imported by
`formal/GaloisForLFunctions/RHTower.lean`.  Their exact targeted builds pass.  The displayed
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Proof chain

```text
von Mangoldt source conductance + integral successor incidence
  -> all logarithmic jets in ell^2
  -> complete finite positive source Gram tower
  -> [OPEN] Gamma/polar Green--Schur identity preserving the Euler source law
  -> normalized prime--archimedean Hankel cone
  -> RH.                                                  (7)
```

## Gates

- [x] prove the discrete logarithmic-jet difference bound
- [x] prove unconditional all-order source-energy summability
- [x] construct the canonical `ell^2` feature vectors
- [x] prove mixed absolute summability and finite Gram positivity
- [x] identify the Gram diagonal with the total source Dirichlet energy
- [x] prove the direct Gram cannot equal any nonempty normalized source Hankel section
- [x] wire, target-build, and audit axioms
- [ ] construct the forced Gamma/polar boundary completion of the graph Laplacian
- [ ] prove Euler-source compatibility of that completion
- [ ] prove the exact Green--Schur moment identity `(6)`
- [ ] RH
