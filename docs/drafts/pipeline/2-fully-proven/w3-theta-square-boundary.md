# W3: the squared-divisor boundary is attained

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** The self-convolution `K=k*k` of the literal theta source has transform `Ξ²`, is strictly positive everywhere, and satisfies `|K(x)|≤C exp(−exp|x|)`. It admits no double-exponential bound with exponent greater than one.

## Proof [PROVED HERE]

The corpus gives `0<k(x)`, continuity, all exponential moments, Fourier transform `Ξ`, and `|k(x)|≤A exp(−exp(2|x|))`. Thus `K` is continuous and strictly positive, and its transform is `Ξ²` by the convolution identity, valid at every complex frequency using the exponential moments.

For `p=exp|t|` and `q=exp|x−t|`, the triangle inequality gives `exp|x|≤pq`. Hence
`p²+q²≥exp|x|+p²/2`, since `pq≤(p²+q²)/2`.
Therefore
`|k(t)k(x−t)|≤A² exp(−exp|x|) exp(−exp(2|t|)/2)`.
Integrating proves the exponent-one bound. The full squared-divisor capacity excludes every larger exponent.

## Consequence

The capacity boundary is sharp even for a nonnegative real spectral square with the exact Xi divisor. Integer blindness is the missing property: `K(log n)>0` for every integer. Neither divisor saturation nor spectral positivity alone supplies an extremal blind function.
