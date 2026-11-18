# A fixed two-pole-free spline with full negative index

Write \(T\) for translation by \(\log4\). The integer spline \(g=(2-5T+2T^2)B\) uses only conductors 1, 4 and 16. Its two pole degrees are \(2-5\cdot2+2\cdot4=0\) and \(2-5/2+2/4=0\). Its Fourier multiplier is \((2z-1)(z-2)\), where \(z=\exp(i\xi\log4)\). Inside \(|\Im\xi|<1/2\) the modulus of \(z\) lies strictly between the two roots. Thus the atom and its reflected transform see every off-line zeta zero. The orientation-index law on integral logarithmic shifts counts all distinct right zeros using only this atom, with both poles identically zero.

For the golden countermodel the same atom has infinite negative index on the lattice of any two distinct primes. Both tests use the actual Fourier multiplier: all off-line zeros in the open strip survive it.

Lean proves `twoPoleDivisor_degrees`, `paperFT_twoPoleAtom_poles`, `twoPoleAtom_integer_index` and `twoPoleAtom_golden_index`. [Two-pole-free integer translates](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TwoPoleFreeIntegerTranslates.lean)
