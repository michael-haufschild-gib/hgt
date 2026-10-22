# Finite modal transfer and Volterra--Haar packet faithfulness

- **ID:** `finite-modal-transfer-volterra-haar-packet-faithfulness`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, exact observation/filter value law
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.FiniteModalTransfer`
  - `GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinVolterraHaarFinitePacket`

## General value law

Let

```text
m_n = sum_i a_i z_i^n
```

be a finite modal observation packet and let a diagonal observation channel multiply mode `i` by
the transfer value `T_i`.  If `H_d` is the leading `d` by `d` Hankel matrix, then

```text
det H_d(Tm) = det H_d(m) * product_i T_i.                 (1)
```

Consequently:

- any transfer zero forces the maximal determinant to vanish;
- if the nodes are distinct and the original amplitudes are nonzero, the filtered determinant is
  nonzero exactly when every transfer value is nonzero;
- under that faithfulness condition, the filtered packet has the same exact noiseless mode count:
  its `d` block is nonsingular and its `d+1` block is singular.

This is an observation-structure theorem.  The natural-number label may record repeated clock
readings, spatial samples, detector bins, or any ordered report; no temporal evolution law is used.

## Critical-Mellin Volterra--Haar specialization

For a finite packet of complex exponents `w_i`, integer sampling gives nodes

```text
z_i = exp(w_i).
```

The already-formalized Volterra--Haar one-mode law rescales each amplitude by

```text
M_L(w_i) = -(2w_i+1)(1-exp(-Lw_i))^2/(2w_i^2).
```

Therefore

```text
det H_d(filtered packet)
  = det H_d(unfiltered sampled packet) * product_i M_L(w_i).   (2)
```

For `L>0` and `Re(w_i)>0`, every factor `M_L(w_i)` is nonzero.  Equation `(2)` then gives the
bidirectional equivalence

```text
det H_d(filtered packet) != 0
  iff det H_d(unfiltered sampled packet) != 0,                 (3)
```

and distinct sampled nodes with nonzero amplitudes retain exact mode count.

## Physics connection

Black-hole ringdown and neutron-star post-merger spectroscopy both organize observable signals as
finite packets of damped complex modes.  Frequency-domain quasinormal-mode filters can deliberately
remove selected black-hole modes by placing transfer zeros at their frequencies; equation `(1)` is
the exact finite-dimensional determinant law separating that operation from a faithful observation
channel.  The same law applies to compact-star mode packets and detector response functions whenever
the relevant transfer values are nonzero.

Primary sources motivating the observation interface:

- S. Ma et al., *Quasinormal-mode filters: a new approach to analyze the gravitational-wave
  ringdown of binary black-hole mergers*, arXiv:2207.10870.
- H. Yang et al., *Gravitational wave spectroscopy of binary neutron star merger remnants with
  mode stacking*, arXiv:1707.00207.
- S. R. Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  arXiv:2210.15935.

## Lean surface

General HTGeometry:

- `finiteModalTransferSequence`
- `det_algebraicHankelMatrix_finiteModalTransferSequence`
- `det_algebraicHankelMatrix_finiteModalTransferSequence_eq_zero_of_transfer_eq_zero`
- `det_algebraicHankelMatrix_finiteModalTransferSequence_ne_zero_iff`
- `finiteModalTransferSequence_exact_hankel_mode_count`

RHTower specialization:

- `criticalMellinVolterraHaarFinitePacket`
- `criticalMellinVolterraHaarFinitePacket_eq_finiteModalTransferSequence`
- `det_criticalMellinVolterraHaarFinitePacket`
- `det_criticalMellinVolterraHaarFinitePacket_ne_zero_iff`
- `criticalMellinVolterraHaarFinitePacket_exact_hankel_mode_count`

## RH relevance and boundary

This closes a real corpus gap: the critical-Mellin filter was previously known to detect one
positive-growth exponential at a time, but the formal corpus did not prove that it preserves the
joint algebraic mode count of an arbitrary finite packet.  The new theorem prevents a proposed
finite-mode source obstruction from being blamed on cancellation introduced by the fixed
Volterra--Haar observation channel.

It is not an RH proof and does not produce the missing lower bound for the actual normalized
Chebyshev source.  It transports any finite-packet nonsingularity certificate through the filter
without loss; the source certificate remains the analytic task.

## Verification

- [x] generic HTGeometry module checks directly
- [x] exact RHTower target builds and is cached
- [x] RHTower consumer checks directly
- [ ] one-sided subpower lower bound for the actual normalized Chebyshev source proved
