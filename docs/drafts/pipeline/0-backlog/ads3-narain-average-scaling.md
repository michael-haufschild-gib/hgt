# One universal arithmetic profile generates every target average

- **ID:** W11-NAS
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Actual target average](../3-formalized/ads3-narain-target-average.md)

## Conjecture

Put `θ(y)=Σ_(n≥1) exp(−πn²y)` and `f(y)=y^(−1/2)θ(y)`.
For every `Y,Z,y>0`, with `A_YZ` the actual double target average,

`A_YZ(y)=YZ A_11(YZy)+2θ(y/(YZ))−2YZθ(YZy)`
`           +2Zf(yZ/Y)+2Yf(yY/Z)−4YZf(YZy)`.

Thus all target dependence of the arithmetic part is a single dilation
and amplitude. The remaining terms are explicit one-dimensional theta
functions. The proposed identity is stronger than equality of pole sets.

At each arithmetic pole `s₀=ρ/2`, it predicts the full principal part
of `F_YZ(s)` is that of `(YZ)^(1−s)F_11(s)`, including multiple poles.
If the pole order is `m` and `a_j` are the Laurent coefficients of
`F_11` at `s₀`, the coefficient at `(s−s₀)^(−k)`, `1≤k≤m`, should be
`(YZ)^(1−s₀) Σ_(j=0)^(m−k) [−log(YZ)]^j a_(−k−j)/j!`.
Thus the leading coefficient has a single dilation factor; lower
principal coefficients mix by an explicit triangular logarithmic law.
The existing pole-order theorem does not establish this coefficient law.
The corpus’s `BlackHoleRingdown.taylorCoeffZero_mul_exp` gives the
finite convolution after clearing a pole and translating its center to
zero. `laurentCoeff_eq_taylorCoeffZero` converts those Taylor coefficients
back to the original Laurent coefficients. This supplies a route to the
triangular law, beyond the fixed-product equality, with all multiplicities
retained; its application remains unformalized.

## Mechanism

Expand the two constant terms in the proved mean Mellin formula.
The coefficient of `L₋²/L₊` is `2(YZ)^(1−s)`; subtracting
`(YZ)^(1−s) F_11(s)` cancels it exactly. The two remaining completed-zeta
terms are the Mellin transforms of the displayed theta corrections.
The corpus's `poissonThetaTail_mellin` identifies the actual theta tail.
Prove absolute Mellin convergence and use inversion on the difference:
its transform is zero on a vertical line, so vertical integrability is
immediate. Positive-height continuity upgrades equality to every `y>0`.

Jacobi inversion should then give

`yA_YZ(y)−(YZy)A_11(YZy)=Y+Z−2+(YZ−1)y+O(exp(−c/y))`

for some `c>0`, with polynomial factors absorbed into a smaller `c`.
This agrees with the candidate main-constant shift
`B_YZ−B_11=Y+Z−2−(3/π)log(YZ)` and would transfer every exponent below
one between all target averages. For the exact subtracted remainder this
would read

`R_YZ(y)=R_11(YZy)+(YZ−1)y+O(exp(−c/y))`.

In particular, two pairs with the same product `YZ` should have
remainders differing by only `O(exp(−c/y))`. Every arithmetic principal
coefficient would agree along each fixed-product family, including at
multiple poles. The ratio `Y/Z` would enter only the exponentially small
correction after main-term subtraction. These consequences remain
unformalized and supply no new arithmetic remainder exponent.

The same cancellation can first be expressed without completed-zeta
normalization. Put `A=ξ(1+2u)`, `B=(1+2u)ξ(2u)/(2u−1)`,
`p_Y=Y^(1/2+u)`, `m_Y=Y^(1/2−u)` and `K=2/[u(1+2u)]`.
Away from `A=0`, direct expansion predicts

`M_YZ−m_Y m_Z M_11=K[A(p_Yp_Z−m_Ym_Z)+B(p_Ym_Z+m_Yp_Z−2m_Ym_Z)]`.

The right side is analytic near every arithmetic resonance: its only
rational denominator zeros are `u=0,±1/2`, outside that divisor.
This would isolate the full arithmetic principal part before source
inversion. Equality at the totalized value of a pole is not claimed;
principal-part comparison uses punctured germs. This algebraic
cancellation and the analytic-germ transfer remain unformalized.
`exists_xi_shift_factor` supplies isolated denominator zeros.
`HTGeometry/MeromorphicLaurentTranslation.lean` supplies punctured-germ
congruence, additivity and vanishing of negative coefficients of an
analytic correction. Since the dilation depends only on `YZ`, these
inputs would prove equality of every negative Laurent coefficient
along fixed-product target families, without a simplicity assumption.

## Entire correction refinement

In the physical variable `s=1/2+u`, the candidate difference
`F_YZ(s)−P^(1−s)F_11(s)` should have only two simple poles:
residue `Y+Z−2` at `s=1`, and residue `P−1` at `s=0`.
Subtracting `(Y+Z−2)/(s−1)+(P−1)/s` should leave an entire function.
The apparent pole at `s=1/2` cancels because each displayed theta
coefficient vanishes there. This refinement needs the exact completed-zeta
expansion and removability proofs; arithmetic-divisor cancellation alone
does not establish the endpoint residues or global entire extension.

## Uniform quantitative consequence

The proposed source identity would also make the VK saving exponent
independent of target heights. Apply the proved unit-height bound at
`Py`, where `P=YZ`, so its clock is `L−log P`. For sufficiently large
`L`, this clock lies between `L/2` and `2L`. Width monotonicity and the
proved doubling estimate retain a fixed fraction of `Lw(L)`, independent
of `P`. The amplitude `√P` changes only the prefactor. The explicit
`(P−1)y` and theta errors decay faster than that bound. Thus one universal
`c>0` should work for every target pair, with target-dependent prefactors
and thresholds. This deduction still requires the exact source scaling
and shifted-profile comparison in Lean. A separate
[direct contour candidate](../1-in-progress/ads3-narain-universal-saving-constant.md)
removes the target-dependent width factor asymptotically and could prove
the stronger explicit exponent `Lw(L)/128` without source scaling.

## Gates

- [ ] 0 → 1: exact mean expansion and actual theta Mellin inputs audited.
- [ ] 1 → 2: Mellin uniqueness, scaling identity and theta error proved.
- [ ] 2 → 3: Lean formalization and transitive axiom audit.
