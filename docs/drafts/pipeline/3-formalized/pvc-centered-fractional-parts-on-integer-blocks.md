# Centered fractional parts on integer blocks

**PVC · Theorem (Lean).** Let $1\le P\le A\le B\le2P$, $Z>0$, and
$\lambda=2Z/(2P)^3$. For every $\Delta>0$,
$$
\left|\sum_{A\le t<B}(\{Z/t\}-1/2)\right|
\ll \Delta P+\Delta^{-1}(P\sqrt\lambda+1/\sqrt\lambda).
$$
All constants are absolute.

**Proof.** At Fourier harmonic $h\ge1$ the second derivative of $hZ/t$ is
between $h\lambda$ and $8h\lambda$. The [integer second derivative test](../../../../formal/GaloisForLFunctions/RHTower/DivisorTerminalModularMean.lean)
bounds the exponential sum by $64P\sqrt{h\lambda}+12/\sqrt{h\lambda}$ when
$h\lambda\le1$. For $h\lambda>1$ the length is already at most $P\sqrt{h\lambda}$.
Conjugation handles negative harmonics. The [sawtooth Fourier decomposition](../../../../formal/GaloisForLFunctions/HTGeometry/SmoothedSawtoothFourier.lean)
gives coefficients of size $O((1+(h\Delta)^2)^{-1}/|h|)$ and
$O(\Delta(1+(h\Delta)^2)^{-1})$. For $h\ne0$ both are
$O(\Delta^{-1}|h|^{-2})$. Their products with $\sqrt{|h|}$ are summable,
and the zero harmonic costs $O(\Delta P)$.

**Lean.** [Integer harmonic and fractional-part bounds](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsOnIntegerReciprocalBlocks.lean) · `integer_reciprocal_fourier_block`, `centered_fractional_reciprocal_integer_block`. Both depend only on `propext`, `Classical.choice`, and `Quot.sound`.
