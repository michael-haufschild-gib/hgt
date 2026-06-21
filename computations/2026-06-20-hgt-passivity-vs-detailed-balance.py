import itertools
import math

import numpy as np


def ergotropy(energies, probs):
    energies = np.asarray(energies, dtype=float)
    probs = np.asarray(probs, dtype=float)
    current = float(np.dot(energies, probs))
    passive_probs = np.sort(probs)[::-1]
    passive_energy = float(np.dot(np.sort(energies), passive_probs))
    return max(0.0, current - passive_energy)


def is_passive(energies, probs, tol=1e-12):
    order = np.argsort(energies)
    p = np.asarray(probs)[order]
    return bool(np.all(p[:-1] + tol >= p[1:]))


def detailed_balance(rates, stationary, tol=1e-10):
    rates = np.asarray(rates, dtype=float)
    stationary = np.asarray(stationary, dtype=float)
    err = 0.0
    for i, j in itertools.combinations(range(len(stationary)), 2):
        err = max(err, abs(stationary[i] * rates[i, j] - stationary[j] * rates[j, i]))
    return err <= tol, err


def node_cases():
    energies = np.array([0.0, 1.0, 2.0])
    gibbs = np.exp(-energies)
    gibbs = gibbs / gibbs.sum()
    inverted = np.array([0.1, 0.2, 0.7])
    passive_nonthermal = np.array([0.5, 0.3, 0.2])
    db_rates = np.array(
        [
            [0.0, 0.2, 0.1],
            [0.2 * gibbs[0] / gibbs[1], 0.0, 0.3],
            [0.1 * gibbs[0] / gibbs[2], 0.3 * gibbs[1] / gibbs[2], 0.0],
        ]
    )
    nondb_rates = np.array([[0.0, 0.9, 0.1], [0.2, 0.0, 0.8], [0.7, 0.2, 0.0]])
    cases = [
        ("gibbs+db", gibbs, db_rates, gibbs),
        ("inverted+db", inverted, db_rates, gibbs),
        ("passive+nondb", passive_nonthermal, nondb_rates, gibbs),
        ("inverted+nondb", inverted, nondb_rates, gibbs),
    ]
    print("NODE: passivity vs detailed balance")
    print("Constraint: passivity is state/Hamiltonian work-extraction; detailed balance is rate-level reversibility.")
    print("case              passive  ergotropy   detailed_balance  db_error")
    for name, probs, rates, stationary in cases:
        db, err = detailed_balance(rates, stationary)
        print(f"{name:17s} {str(is_passive(energies, probs)):7s}  {ergotropy(energies, probs):9.5f}   {str(db):16s} {err:.5g}")


def fe_symmetric(zeros, tol=1e-9):
    unused = list(zeros)
    while unused:
        z = unused.pop()
        target = 1.0 - z
        found = None
        for i, w in enumerate(unused):
            if abs(w - target) <= tol:
                found = i
                break
        if found is None:
            return False
        unused.pop(found)
    return True


def off_line_count(zeros, tol=1e-9):
    return sum(abs(z.real - 0.5) > tol for z in zeros)


def ht_cases():
    cases = {
        "rh+fe": [0.5 + 14.1j, 0.5 - 14.1j, 0.5 + 21.0j, 0.5 - 21.0j],
        "off_line_fe": [0.4 + 14.1j, 0.6 - 14.1j, 0.6 + 14.1j, 0.4 - 14.1j],
        "rh_no_fe": [0.5 + 14.1j, 0.5 + 21.0j, 0.5 + 25.0j, 0.5 + 30.0j],
        "off_line_no_fe": [0.3 + 14.1j, 0.55 + 21.0j, 0.7 - 19.0j, 0.5 - 30.0j],
    }
    print("\nSTEP8/9 HT transfer")
    print("Minimal edit: detailed balance -> FE mirror pairing; passivity -> no off-line zero directions.")
    print("Method #23 classify boundary cases.")
    print("case              FE_balance  passive_line  off_line_count  kappa_minus_proxy")
    for name, zeros in cases.items():
        fe = fe_symmetric(zeros)
        off = off_line_count(zeros)
        print(f"{name:17s} {str(fe):10s}  {str(off == 0):12s} {off:14d} {off // 2:18d}")


if __name__ == "__main__":
    node_cases()
    ht_cases()
