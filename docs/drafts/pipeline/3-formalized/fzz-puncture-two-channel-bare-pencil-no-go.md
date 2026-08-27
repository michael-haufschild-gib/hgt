# FZZ puncture fixed two-channel bare-pencil no-go

- **ID:** FZZ-P-BA2
- **Stage:** 3-formalized
- **Type:** SPECTRAL PENCIL CLASSIFICATION / NO-GO SURVIVOR
- **Parent:** FZZ-P-GDSC
- **Frontier-map policy:** read only; no edit made

## Exact result

Fix a complex two-channel interior matrix `A₀=[[a,b],[c,d]]` and nonzero
coupling row `(p,q)`.  A dark eigenmode at real energy `E` is a nonzero vector
`x` satisfying `px₀+qx₁=0` and `A₀x=Ex`.

1. Dark eigenmode exists exactly when canonical dark vector `(q,-p)` satisfies
   `aq-bp=Eq` and `cq-dp=-Ep`.
2. Two dark eigenmodes for fixed `A₀,p,q` necessarily have same energy.
3. Adding coupling-sourced affine FZZ continuum mode gives exact additional
   condition `q d₀-p d₁≠0`.
4. No fixed two-channel bare pencil can realize every positive real zero of
   `XiC`: corpus Hardy theorem supplies two distinct such zeros, while the dark
   pencil supports at most one energy.

Fourth statement is unconditional and quantified over all complex matrix,
coupling, and slope coefficients.

## Paper proof

Because `(p,q)≠(0,0)`, its kernel is the line spanned by `(q,-p)`.  Eliminating
an arbitrary nonzero dark vector from `A₀x=Ex` gives the two displayed canonical
equations; conversely `(q,-p)` witnesses them.

If energies `E,F` both satisfy those equations, use `q≠0` in first coordinate
or `p≠0` in second to cancel the nonzero coefficient and obtain `E=F`.
The earlier coupling-sourced Plücker classification supplies exactly transverse
slope condition.  Finally apply the unique-energy theorem to two distinct
positive real `XiC` zeros furnished unconditionally by Hardy's theorem.

## No-go closure and positive survivor

Fixed two-channel `A₀-EI` dynamics is now closed as FZZ-P completeness route: it
cannot cover even two known critical-line zeros, hence cannot cover full divisor.

Strongest positive survivor: viable FZZ dynamics must include at least one of:

- genuinely nonlinear/meromorphic energy-dependent interior operator `A(E)`;
- energy-dependent coupling and moving dark line `ker K(E)`;
- infinite-dimensional dark sector supporting multiple bare eigenenergies.

Any such extension still owes exact common-kernel incidence and nonzero
transverse continuum jet; neither may be fitted to Xi zeros.

## Hostile review

- The no-go is for fixed two-channel interior matrix, not arbitrary nonlinear
  self-energy or infinite GFZZ state space.
- Self-adjointness is not needed, making obstruction stronger.
- Point-mode condition includes nonzero amplitude, nonzero coupling row, source
  node, and transverse slope.
- Contradiction uses proved unconditional Hardy zeros, not RH.
- `XiC` coverage is a diagnostic completeness target; theorem does not identify
  an independent cigar divisor with `XiC`.

## Novelty audit (2026-08-27)

Corpus search found affine FZZ channels, Gram-dark reduction, general affine
Hermitian pencils, and unconditional distinct `XiC` zeros, but no fixed dark-line
spectral-pencil obstruction joined to FZZ completeness.  Primary literature on
multilevel Friedrichs bound states and emitter-array BICs studies energy-dependent
form factors and multiple resonant values; search found no exact FZZ/Hardy
two-zero no-go.  Linear-algebraic uniqueness itself is elementary; novelty claim
is precise route closure and resulting necessary model enlargement. Priority is
provisional pending expert review.

Primary comparison sources:

- arXiv:quant-ph/0510058, *Bound-state eigenenergy outside and inside the
  continuum for unstable multilevel systems*
- arXiv:1904.13004, *Bound states in the continuum for an array of quantum
  emitters*
- arXiv:2109.02939, *The self-energy of Friedrichs-Lee models and its application
  to bound states and resonances*

## Lean realization

Module:
`GaloisForLFunctions.RHTower.FZZCigarPunctureTwoChannelBarePencilNoGo`

Theorems:

- `fzzPunctureTwoChannelBareDarkEigenmode_iff`
- `fzzPunctureTwoChannelBareDarkEigenmode_energy_unique`
- `fzzPunctureTwoChannelBarePencilPointMode_iff`
- `fzzPunctureTwoChannelBarePencilPointMode_energy_unique`
- `not_fzzPunctureTwoChannelBarePencilXiComplete`

Verification:

- direct `lake env lean` passed
- targeted module `lake build` passed
- exported theorem axiom audit passed: only standard Mathlib axioms
- imported by `GaloisForLFunctions.RHTower`
