import numpy as np

sx = np.array([[0, 1], [1, 0]], complex)
sy = np.array([[0, -1j], [1j, 0]], complex)
sz = np.array([[1, 0], [0, -1]], complex)

def hypertranscendental(z, terms=40):
    z = np.asarray(z, dtype=complex)
    out = np.zeros_like(z, dtype=complex)
    fact = 1.0
    for n in range(1, terms + 1):
        fact *= n
        out += z ** (n * n) / fact
    return out

def H(R):
    x, y, z = R
    return x * sx + y * sy + z * sz

def normalize_R(R, eps=1e-12):
    R = np.array(R, dtype=float)
    n = np.linalg.norm(R)
    if n < eps:
        return np.array([0.0, 0.0, 1.0])
    return R / n

def ground(R):
    w, v = np.linalg.eigh(H(normalize_R(R)))
    return v[:, 0]

def fidelity_vs_speed(Ttot, N=4000):
    ts = np.linspace(0, 1, N); dt = (ts[1] - ts[0]) * Ttot
    psi = ground((0, 0, 1.0))
    for t in ts:
        th = np.pi * t
        q = hypertranscendental(0.22 * np.exp(2j * np.pi * t))
        R = normalize_R((0.30*np.sin(th)+0.08*np.real(q), 0.08*np.imag(q), np.cos(th)))
        Hm = H(R); U = np.linalg.inv(np.eye(2)+0.5j*dt*Hm)@(np.eye(2)-0.5j*dt*Hm)
        psi = U @ psi; psi = psi/np.linalg.norm(psi)
    g = ground((0.0, 0.0, -1.0)); return abs(np.vdot(g, psi))**2

for Ttot in [1, 5, 20, 80, 200]:
    print("Ttot", Ttot, "fidelity", fidelity_vs_speed(Ttot))

def berry_phase(theta, N=4000):
    phis = np.linspace(0, 2*np.pi, N, endpoint=False); states = []
    for p in phis:
        q = hypertranscendental(0.18*np.exp(1j*p)); ripple = 1.0 + 0.10*np.real(q)
        R = normalize_R((ripple*np.sin(theta)*np.cos(p), ripple*np.sin(theta)*np.sin(p), np.cos(theta)+0.05*np.imag(q)))
        states.append(ground(R))
    prod = 1.0+0j
    for k in range(N):
        ov = np.vdot(states[k], states[(k+1)%N]); prod *= ov/abs(ov)
    return -np.angle(prod)

for th in [0.5, 1.0, 1.5, 2.0]:
    print("theta", th, "berry", berry_phase(th))
