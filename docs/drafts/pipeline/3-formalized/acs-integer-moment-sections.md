# Integer moment kernels with small sections

For each integer $B\ge1$ there is a $k$ independent of $N$ such that every nonzero integer divisor supported on $N/B<d\le N$ with $\sum_d a_d d^j=0$ for $0\le j<k$ has positive Weil degree. At every sufficiently large multiplicity its original radius admits a nonzero rational section, and its ordinary logarithmic section count recovers the signed degree in the Tate limit. The threshold may depend on the divisor.

## Proof

Translate the spline packet into $[-A,0]$ with $A=\log B+8$. Suppose a sequence of unit squared mass annihilates successively more exponential moments while its Weil energies stay below $E$. On the fixed support, polynomials in $e^u$ approximate each Fourier character uniformly. The common $L^1$ bound then forces pointwise decay of the Fourier transforms. Dominated convergence sends the mass of every fixed frequency band to zero. Bounded Weil energy bounds the high-frequency tails uniformly on this window. Plancherel contradicts unit mass.

The $j$th exponential moment of the spline translated by $\log d$ is $d^j$ times the strictly positive moment of the original spline. A common translation multiplies this row by a positive scalar. The Vandermonde determinant gives injectivity of the packet map. Normalization and the preceding bound with $E=0$ give strict positivity. The signed degree limit puts the generator inside its original radius.

The rational kernel has dimension at least $N-\lfloor N/B\rfloor-k$. Given $\varepsilon>0$, take $B>2/\varepsilon$ and then $N>2k/\varepsilon$. The resulting subspace has dimension at least $(1-\varepsilon)N$, and clearing denominators gives an integral representative on each rational ray. The divisor $e_1+e_p$ has zeroth moment two.

## Lean

[ExponentialMomentsForcePositiveWeilEnergy.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ExponentialMomentsForcePositiveWeilEnergy.lean) proves `unit_weil_energy_of_vanishing_moments`. [SmallSectionsOnTheIntegerMomentKernel.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/SmallSectionsOnTheIntegerMomentKernel.lean) proves `windowMomentKernel_rank`, `windowMomentKernel_smallSections` and `smallSections_on_subspaces_of_density_one`.
