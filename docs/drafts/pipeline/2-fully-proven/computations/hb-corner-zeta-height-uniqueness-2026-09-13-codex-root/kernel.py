import mpmath as mp


def primitive_power(k, q0, q1):
    return mp.log(q1 / q0) if k == 5 else (mp.power(q1, k - 5) - mp.power(q0, k - 5)) / (k - 5)


def hmn(m, n, L, z):
    d = L - z
    q0, q1 = d - 1, d + 1
    total = mp.mpc(0)
    for i in range(m + 1):
        for j in range(n + 1):
            coef = mp.binomial(m, i) * mp.binomial(n, j) * mp.power(-L, m - i) * mp.power(-d, n - j)
            total += coef * primitive_power(i + j, q0, q1)
    return total


def fmn(m, n, delta, L, z):
    exponent = delta if (m, n) in ((1, 1), (1, 3)) else delta - 2
    return mp.power(L, exponent) * hmn(m, n, L, z)


def dstar_f33(delta, L, z):
    dLL = mp.diff(lambda x: x * x * fmn(3, 3, delta, x, z), L, 2)
    dzz = mp.diff(lambda y: L * L * fmn(3, 3, delta, L, y), z, 2)
    return dLL - dzz


def coefficients(s, t):
    lam = (s + 1) * (s + 2)
    A0 = (5 * lam - 6) / 4
    ks, kt = s * (s - 1) / 4, t * (t - 1) / 4
    alphas, alphat = ks * (s + 2) * (2 * s + 3), kt * (t + 2) * (2 * t + 3)
    betas, betat = -ks / 2, -kt / 2
    return A0, alphas, alphat, betas, betat


def corner(s, t, delta, L):
    z = 1 - L
    A0, alphas, alphat, betas, betat = coefficients(s, t)
    f13 = fmn(1, 3, delta, L, z)
    f31 = fmn(3, 1, delta, L, z)
    f33 = fmn(3, 3, delta, L, z)
    deriv = dstar_f33(delta, L, z)
    cR = L * L * (A0 * betas * f13 + A0 * betat * f31 +
                    (alphas * betat + betas * alphat) * f33 + betas * betat * deriv)
    cD = L * L * betas * betat * f33
    return cR, cD


def observable(rho, L):
    s, t, delta = rho - 2, -rho - 1, 2 * rho - 1
    a = corner(s, t, delta, L)
    b = corner(t, s, -delta, L)
    W = (a[0] - b[0], a[1] - b[1])
    return W, -W[0] / W[1]


def diagnostic(sigma, height, L):
    W, ratio = observable(mp.mpc(sigma, height), L)
    scale = abs(W[0]) * abs(W[1])
    score = -mp.im(W[0] * mp.conj(W[1])) / scale
    return score, abs(W[0]), abs(W[1]), mp.im(ratio)
