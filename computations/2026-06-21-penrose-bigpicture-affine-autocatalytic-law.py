import math


k = 1.25
M = 10.0
x0 = 0.2
a0 = M - x0
h = 0.001
T = 5.0
steps = int(T / h)


def rk4(a, x):
    def f(aa, xx):
        rate = k * aa * xx
        return -rate, rate

    k1a, k1x = f(a, x)
    k2a, k2x = f(a + 0.5 * h * k1a, x + 0.5 * h * k1x)
    k3a, k3x = f(a + 0.5 * h * k2a, x + 0.5 * h * k2x)
    k4a, k4x = f(a + h * k3a, x + h * k3x)
    return (
        a + h * (k1a + 2 * k2a + 2 * k3a + k4a) / 6,
        x + h * (k1x + 2 * k2x + 2 * k3x + k4x) / 6,
    )


a, x = a0, x0
max_mass_error = 0.0
samples = []
for n in range(steps + 1):
    t = n * h
    if n % 1000 == 0:
        logit = math.log(x / a)
        initial_rate = k * a0
        unconstrained = x0 * math.exp(initial_rate * t)
        samples.append((t, a, x, logit, unconstrained))
    max_mass_error = max(max_mass_error, abs((a + x) - M))
    if n < steps:
        a, x = rk4(a, x)

print("Autocatalytic law: conserved pool vs unconstrained growth")
print(f"max_mass_error={max_mass_error:.3e}")
print("t       a(t)        x(t)        log(x/a)    exp_same_initial_rate")
for t, aa, xx, logit, expx in samples:
    print(f"{t:4.1f} {aa:11.6f} {xx:11.6f} {logit:11.6f} {expx:18.6f}")

expected_slope = k * M
observed = []
for (t0, _, _, l0, _), (t1, _, _, l1, _) in zip(samples, samples[1:]):
    observed.append((l1 - l0) / (t1 - t0))
print(f"expected_logit_slope={expected_slope:.6f}")
print("observed_logit_slopes=" + ",".join(f"{v:.6f}" for v in observed))
