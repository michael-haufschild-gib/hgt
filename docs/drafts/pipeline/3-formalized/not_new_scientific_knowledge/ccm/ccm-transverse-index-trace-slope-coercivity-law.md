# Every transverse divisor unit costs more than four units of CCM trace slope

- **ID:** `ccm-transverse-index-trace-slope-coercivity-law`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** prime-zeta divisor monodromy, shifted-Xi leakage index, and the Hankel
  gap-trace slope identity
- **Statement:** The integer transverse divisor charge and the metric residue charge obey a sharp
  strip coercivity law: every right-half Xi zero, counted with multiplicity, contributes strictly
  more than four units to the negative initial Hankel trace slope. The incoming Euler pole carries
  one unit with exactly four. Hence a nonexpansive pole-to-divisor trace transfer forces zero
  transverse index and RH.

## 1. Quantized and metric charges

Write the right-half nontrivial Xi divisor as

```text
rho_j=1/2+a_j+i gamma_j,
0<a_j<1/2,
m_j=ord_(rho_j)(Xi).                                      (1)
```

For a finite sub-divisor `D`, define its quantized transverse charge

```text
kappa(D)=sum_j m_j.                                       (2)
```

This integer has three equivalent established realizations:

1. the degree of the denominator inner factor of the shifted-Xi quotient;
2. the rank/multiplicity of the corresponding Hardy leakage channel;
3. the total prime-zeta monodromy around the selected zero contours.

Define the metric charge by the anti-causal residue profile

```text
ell_D(t)=2 sum_j m_j exp(-(a_j+i gamma_j)t)               (3)
```

and its shifted Hankel gap trace `F_D`:

```text
F_D(u)=Tr(H_(D,u)^*H_(D,u)),
(H_(D,u)f)(x)=integral_0^infinity ell_D(u+x+y)f(y)dy.     (4)
```

The trace-slope theorem gives

```text
E(D):=-F_D'(0+)=||ell_D||_2^2.                            (5)
```

## 2. Index--slope coercivity

For every nonempty finite right-half divisor,

```text
E(D)>4 kappa(D).                                          (6)
```

### Proof

The positive Cauchy Gram formula and its diagonal bound give

```text
E(D)
 =4 sum_(j,k)m_jm_k
   (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2)
 >=2 sum_j m_j^2/a_j.                                    (7)
```

Since every `a_j<1/2`,

```text
2m_j^2/a_j>4m_j^2>=4m_j.                                 (8)
```

Summing `(8)` and using `(7)` proves `(6)`.

If the right-half divisor is infinite, its finite sub-divisors have unbounded integer charge.
Their diagonal energies exceed `4 kappa(D)` and the Cauchy cross terms are positive. Thus the
extended metric charge is `+infinity`. Equation `(6)` therefore persists in the extended sense.

## 3. The incoming pole saturates the unit cost

The finite-prime completed source has one upper pole, at transverse depth `1/2`, with profile

```text
ell_pole(t)=2 exp(-t/2).                                  (9)
```

Give it the source charge

```text
kappa_pole=1.                                             (10)
```

Its gap trace is

```text
F_pole(u)=4 exp(-u),
E_pole=-F_pole'(0+)=4=4 kappa_pole.                       (11)
```

Thus the boundary of the critical strip is the exact unit-cost threshold. A pole at depth
`1/2` costs four; every divisor unit strictly inside the strip costs more than four.

## 4. Positive conservation theorem sufficient for RH

Suppose the completed Euler--Gamma source constructs a pole-to-divisor transfer that preserves the
quantized marking and does not increase initial trace loss:

```text
E(D_Xi)<=E_pole=4.                                       (12)
```

Combining `(6)` and `(12)` gives

```text
4 kappa(D_Xi)<E(D_Xi)<=4                                 (13)
```

whenever `kappa(D_Xi)>0`, which is impossible because `kappa(D_Xi)` is an integer. Therefore

```text
kappa(D_Xi)=0,
```

so there is no right-half zero and RH follows by the functional equation.

The positive statement is a resource allocation law:

```text
one incoming pole unit with budget 4
  -> completed source/divisor incidence
  -> each outgoing transverse unit costs strictly more than 4
  -> nonexpansive completion permits no outgoing unit.   (14)
```

## 5. Relation to finite-prime monodromy and the pointed graph

Raw finite Euler exponentials have zero divisor winding. Their completion nevertheless contains
the distinguished pole unit `(9)`. In the all-prime limit that pole is cancelled, while any
off-line Xi divisor would reappear as nonliftable monodromy/rank in the anti-causal graph.

The canonical closed two-channel source graph realizes the same transition. A rational orbit
insertion adds one rank-one residue coordinate per right-half zero; its trace-slope cost is the
inverse-horizontal metric in `(7)`. Hence a viable CCM construction must transport the pair

```text
(integer boundary index, initial trace slope),            (15)
```

not either coordinate alone. The integer prevents a remote divisor packet from dissolving in a
limit, while the slope supplies the strict critical-strip cost that selects the zero-index chamber.

This also reconciles the topological and semilocal formulations in the corpus:

```text
prime-zeta/winding charge       = quantized coordinate,
Hankel gap-trace derivative     = metric coordinate,
exact Euler source marking      = orientation selecting their coupling.       (16)
```

## 6. Exact remaining theorem

The coercivity `(6)` is unconditional once the divisor is present. It does not prove the source
budget `(12)`. The sole RH-bearing theorem on this interface is:

```text
close the exact Xi two-channel graph;
construct its shifted anti-causal traces from Euler--Gamma data;
prove their initial loss does not exceed the incoming value 4.                (17)
```

No finite positivity test, fixed-aperture trace, unpointed HT invariant, or ordinary Hardy
contractivity proves `(17)`. It is an endpoint trace-slope theorem on the distinguished cofinal
source.

## 7. Scientific classification and Lean decision

Equation `(6)` is the diagonal Cauchy-energy bound plus the classical strip width `a_j<1/2`.
Its index interpretation is a useful bridge among existing parent theories, not new scientific
knowledge. New scientific content would be an unconditional proof of `(17)`.

The Lean tree contains finite topological ancestor and rational-quartet marking results, but not
the analytic trace-slope carrier. Formalizing only the integer inequality would not certify the
source budget, so no Lean file is added.

## Gates

- [x] quantized divisor charge identified across inner degree, leakage, and monodromy
- [x] metric charge identified with initial Hankel trace loss
- [x] strict coercivity `E(D)>4 kappa(D)`
- [x] incoming pole shown to saturate `E=4 kappa`
- [x] nonexpansive marked transfer shown sufficient for RH
- [ ] source proof of the four-unit trace budget
- [ ] RH

## Lean status

**Formalized unconditionally, 2026-08-15**, in
`formal/GaloisForLFunctions/RHTower/CCMTransverseIndexTraceSlopeCoercivity.lean`, on the divisor
profile and half-line exponential integral of
`RHTower/CCMShiftCovariantPoleDivisorCapacity.lean`.

- `divisorPacketEnergy` — the right-hand side of `(5)`, `E(D) = ||ell_D||_2^2`, defined as the
  `L^2(0, infinity)` energy of the anti-causal residue profile `(3)`.
- `cauchyWeight`, `cauchyWeight_pos`, `cauchyWeight_self`, `re_div_add_conj` — the positive Cauchy
  weight `(a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2)` and its identification with the real part of
  the resolvent pairing.
- **`ofReal_divisorPacketEnergy`**, **`divisorPacketEnergy_eq`** — equation `(7)`, first half: the
  energy is the exact positive Cauchy form `4 sum_(j,k) m_j m_k (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2)`.
  Proved by expanding `|ell_D|^2 = ell_D conj(ell_D)` into a double exponential sum and integrating
  each term.
- **`diagonal_le_divisorPacketEnergy`** — equation `(7)`, second half: every Cauchy term is positive,
  so the energy dominates its own diagonal `2 sum_j m_j^2 / a_j`.
- **`four_mul_multiplicity_lt_divisorPacketEnergy`** — equations `(6)`, `(8)`: for a nonempty packet
  with `0 < a_j < 1/2` and `m_j >= 1`, `E(D) > 4 kappa(D)`.
- `polePacketEnergy`, **`polePacketEnergy_eq_four`** — equation `(11)`: the incoming pole at
  transverse depth `1/2` has energy exactly `4`.
- **`divisorPacket_isEmpty_of_energy_le_pole`** — equation `(13)`: a nonexpansive pole-to-divisor
  transfer admits no divisor unit at all.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized here, and imported: the trace-slope identity `(5)` itself, i.e. the identification of
`-F_D'(0+)` with `||ell_D||_2^2`, which is the content of
`ccm-hankel-gap-trace-slope-rh-criterion.md`; the three realizations of the quantized charge listed
in section 1; and the source budget `(12)`, which the card explicitly leaves open.
