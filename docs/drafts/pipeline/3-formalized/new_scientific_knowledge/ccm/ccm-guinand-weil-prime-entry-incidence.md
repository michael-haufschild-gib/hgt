# CCM Guinand--Weil four-unit prime-entry incidence

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / aperture-event connection
- **Novelty scope:** corpus-new all-integer-mode odd/diagonal incidence and exact weighted-cosine
  event tangent; prior corpus already proves one-sided first-clock odd entry slope tomography
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMGuinandWeilPrimeEntryIncidence.lean`

## Entry wall

`CCMFirstClockPrimeEntrySlopeTomography` already proves that the first-clock odd atom enters
continuously with a source-marked one-sided slope in full-aperture coordinate `L`. The result here
does not claim that base fact as new. It transports the event to half-aperture `a=L/2`, embeds it in
the literal Guinand--Weil horizon reporter, extends it to every integer mode, and adds the previously
missing weighted-cosine diagonal tangent.

Index `k>1` reaches the moving horizon at

```text
a_k=log(k)/2,
omega_k(a)=1-(log(k)/2)/a.                                     (1)
```

Lean proves

```text
omega_k(a_k)=0,
omega'_k(a_k)=2/log(k).                                        (2)
```

The odd and diagonal profiles are exactly the single-atom terms in the existing continuous-source
reporter:

```text
b_(k,n)(omega)= -w_k sin(2*pi*n*omega)/pi,
d_(k,n)(omega)= -2 w_k omega cos(2*pi*n*omega),                 (3)
```

where `w_k=criticalMellinAtomWeight(k)`.

## Four-unit incidence

Both source values vanish at entry, so adding an atom at the boundary creates no value jump:

```text
b_(k,n)(omega_k(a_k))=d_(k,n)(omega_k(a_k))=0.                  (4)
```

Their aperture tangents are nonzero and exact:

```text
d/da b_(k,n)(omega_k(a))|_(a=a_k) = -4 n w_k/log(k),
d/da d_(k,n)(omega_k(a))|_(a=a_k) = -4 w_k/log(k).              (5)
```

Therefore

```text
b'_(k,n)(a_k)=n d'_(k,n)(a_k).                                 (6)
```

Equation `(6)` is a literal pre-quotient source--codiagonal incidence, and the coefficient four is
forced by two factors of two: physical Fourier phase and horizon-entry velocity. The diagonal
event tangent is mode-independent, matching the mode-independent Gamma first-jet phenomenon.

## Pivot forced by the theorem

Finite truncation aperture is not the same smooth parameter as the corpus's Julia/Ward phase
aperture. Prime inclusion is one-sided at the walls `(1)`. A global bridge must therefore be a
BV/jump or event-resolved connection whose atomic residues obey `(5)`, not a naive everywhere
ordinary derivative of the floor-truncated source.

## Lean declarations

- `ccmGuinandWeilPrimeEntryAperture`
- `ccmGuinandWeilPrimeEntryHorizon`
- `hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_entry`
- `ccmGuinandWeilPrimeEntryOddProfile_eq_sourceAtom`
- `ccmGuinandWeilPrimeEntryDiagonalProfile_eq_sourceAtom`
- `ccmGuinandWeilPrimeEntryOddGerm_at_entry`
- `ccmGuinandWeilPrimeEntryDiagonalGerm_at_entry`
- `hasDerivAt_ccmGuinandWeilPrimeEntryOddGerm_entry`
- `hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGerm_entry`
- `ccmGuinandWeilPrimeEntry_fourUnit_source_codiagonal_incidence`

Targeted direct Lean check and `lake build
GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilPrimeEntryIncidence` pass. Principal `#print axioms`
reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
