# SZ contraction estimate for the actual remainder source

- ID: sz-actual-remainder-source-contraction
- Stage: 3-formalized
- Type: THEOREM (Lean)
- Route: SZ
- RH status: unresolved

## New actual-source result

Let B_a be the literal bounded Weil remainder, c_a its prescribed Suzuki
interval shift, H_a=B_a/c_a, and p_a=(p_+-p_-)/2. Put
D=norm(kappa)+46 and C0=2*D. For every fixed K>0 and epsilon>0,
eventually in positive aperture a, every natural n satisfies

    norm(H_a^(n+1) p_a) <= epsilon*norm(H_a^n p_a)
      + (4*D/pi)*C0^n*exp(a/2)/sqrt(exp(K*a)).

The quantifier over n is uniform after choosing the aperture threshold.
All source budgets are discharged by the actual-orbit theorem. No
regularity of the unknown Riesz response is assumed. The complete prime
sum retains every prime power and the original terminal cutoff.

## Exact operator proof

The full-line profile g_a is the sum of exp(h/2) and exp(-h/2) on
[-2a,2a], zero outside. At x,y in [-a,a], g_a(x-y) is exactly the sum
of the two crossed exponential products. Actual aperture support and
the L2 inner-product integral therefore identify compression of its
Schur convolution operator with ccmPolarOperator, for every aperture
L2 vector.

The exact complex Fourier integral is polarMultiplier(a,-2*pi*xi).
Its positive L1 mass is 8*sinh(a), giving global convolution norm at
most 4*exp(a). The full prime translation operator has norm at most
42*exp(a), using the complete critical Mangoldt weights. Adding the
scalar atom gives full-line norm at most D*exp(a). Its aperture
compression is exactly the actual bounded remainder, and its Fourier
cofunction has symbol

    kappa + polarPrimeStieltjesSymbol(a,-2*pi*xi).

The earlier exponential-frequency cancellation, on an enlarged fixed
band, absorbs the Fourier normalization factor 2*pi. The fixed scalar
atom is also negligible compared with exp(a). Hence the full symbol
is at most (epsilon/2)*exp(a) on abs(xi)<=exp(K*a), eventually.

Apply the exact Fourier identity to the low-frequency cutoff of a
source f. L2 cofunction comparison gives the retained-band operator
bound. The complementary source costs at most the full-line global
norm times its Fourier tail. The previously audited finite-source
tail gives norm(tail)<=2*V/(pi*sqrt(R)). Physical compression is
contractive. Finally exp(a)<=2*c_a proves

    norm(H_a f) <= epsilon*norm(f) + (4*D/pi)*V/sqrt(R).

Substitute the unconditional actual orbit budget V=C0^n*exp(a/2) and
R=exp(K*a) to obtain the stated recurrence.

## Verification

- CCMRestrictedWeilPolarConvolution: nine public theorems; final leaf
  audit71723 exited0 without warnings.
- CCMRestrictedWeilRemainderMultiplier: seven public theorems; final
  leaf audit23929 exited0 without warnings.
- CCMRestrictedWeilSourceContraction: three public theorems; scratch
  audit79461 and final leaf audit94938 exited0 without warnings.

Each final audit used `lake --old env lean <leaf> -o <leaf.olean>`.
All three leaves are wired into the root RHTower umbrella. No umbrella
or full build was run. All nineteen public theorem axiom queries passed
in scratch82012, reporting only propext, Classical.choice and Quot.sound.
No added axioms or proof placeholders occur.

Post-wiring lint29335 exits1 on eleven unrelated unreachable modules,
listed in the working log. None of these three new leaves is reported.
Global lint is not green; unrelated work is preserved.

## Remaining hard proof

Solve this recurrence through a number of steps growing with aperture,
bound the finite Neumann sum and residual, and use the actual odd Riesz
equation to obtain uniform odd energy. The exact raw odd source equation
already exists as suzukiTaRawCoalescingOdd_inner; the coordinate transport
must still be retained in the energy argument. The original signed
Wronskian, canonical normalization, shift removal and RH remain open.
