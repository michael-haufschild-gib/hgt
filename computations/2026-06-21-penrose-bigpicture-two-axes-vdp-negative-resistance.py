import math

mu = 1.0
h = 0.001
T = 60.0
steps = int(T/h)
initials = [(0.1,0.0),(1.0,0.0),(4.0,0.0)]

def f(state):
    x, v = state
    return (v, mu*(1-x*x)*v - x)

def rk4(state):
    x, v = state
    k1 = f((x,v))
    k2 = f((x+0.5*h*k1[0], v+0.5*h*k1[1]))
    k3 = f((x+0.5*h*k2[0], v+0.5*h*k2[1]))
    k4 = f((x+h*k3[0], v+h*k3[1]))
    return (x + h*(k1[0]+2*k2[0]+2*k3[0]+k4[0])/6,
            v + h*(k1[1]+2*k2[1]+2*k3[1]+k4[1])/6)

def integrate(x0, v0):
    state = (x0, v0)
    max_r_last = 0.0
    min_r_last = 1e9
    pos_power = 0
    neg_power = 0
    power_sum = 0.0
    last_window_start = int(40.0/h)
    crossing_peaks = []
    prev_v = state[1]
    for n in range(steps):
        x, v = state
        p = mu*(1-x*x)*v*v
        if n >= last_window_start:
            r = math.sqrt(x*x+v*v)
            max_r_last = max(max_r_last, r)
            min_r_last = min(min_r_last, r)
            power_sum += p*h
            if p >= 0:
                pos_power += 1
            else:
                neg_power += 1
        state = rk4(state)
        if n >= last_window_start:
            x2, v2 = state
            if prev_v > 0 and v2 <= 0:
                crossing_peaks.append(x2)
            prev_v = v2
    return {
        'initial': (x0,v0),
        'final': state,
        'last_radius_range': (min_r_last, max_r_last),
        'net_energy_change_last20': power_sum,
        'positive_power_fraction': pos_power/(pos_power+neg_power),
        'last_positive_peaks': crossing_peaks[-5:],
    }

def avg_r(r0):
    r = r0
    dt = 0.01
    for _ in range(int(T/dt)):
        # RK4 for averaged amplitude
        g = lambda rr: 0.5*mu*rr*(1-rr*rr/4)
        k1 = g(r)
        k2 = g(r+0.5*dt*k1)
        k3 = g(r+0.5*dt*k2)
        k4 = g(r+dt*k3)
        r += dt*(k1+2*k2+2*k3+k4)/6
    return r

print('Van der Pol negative-resistance energy balance')
for x0, v0 in initials:
    out = integrate(x0, v0)
    print(f"initial={out['initial']} final=({out['final'][0]:+.4f},{out['final'][1]:+.4f}) "
          f"last_radius_range=({out['last_radius_range'][0]:.4f},{out['last_radius_range'][1]:.4f}) "
          f"net_dE_last20={out['net_energy_change_last20']:+.6f} "
          f"pos_power_frac={out['positive_power_fraction']:.3f} "
          f"last_peaks={[round(p,4) for p in out['last_positive_peaks']]}")
print('Averaged amplitude equation terminal radii')
for r0 in [0.1,1.0,4.0]:
    print(f"r0={r0:.1f} -> r(T)={avg_r(r0):.8f}")
