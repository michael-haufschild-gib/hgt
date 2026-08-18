# Horizontal entry transfers off-line charge into multiplicity charge

- **ID:** horizontal-entry-charge-transfer
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent theory:** elementary multiset algebra; horizontal multiplicity and symmetric-diagonal
  terms in the 2025--2026 pair-correlation literature; the in-tree winding/deck-charge motion API

## Statement

Let `Z_I` be the finite multiset of nontrivial zeros of a self-dual completed function whose
ordinates lie in a bounded interval `I` avoiding zeros at its endpoints. Assume that `Z_I` is
stable under

```text
rho |-> 1-conj(rho)
```

and write `m_rho` for the multiplicity of a distinct zero. For each ordinate `gamma`, put

```text
H_gamma = sum_(Im rho = gamma) m_rho.
```

Define four integer statistics

```text
N_I = sum_rho m_rho,
C_I = sum_gamma H_gamma^2,
D_I = sum_rho m_rho^2,
O_I = C_I-D_I,
M_I = D_I-N_I.
```

Then:

1. `O_I` and `M_I` are nonnegative even integers.
2. `O_I=0` if and only if every zero in `Z_I` lies on the critical line.
3. The horizontal-multiplicity excess splits exactly as

   ```text
   C_I-N_I = O_I+M_I.                                  (1)
   ```

4. When a simple reflected off-line pair collides into a double zero on the critical line,

   ```text
   (O_I,M_I) : (2,0) -> (0,2),
   C_I-N_I   : 2     -> 2.                              (2)
   ```

   More generally, if the pair collides with an existing critical-line zero of multiplicity
   `r`, the transfer is

   ```text
   (O_I,M_I) : (4r+2, r^2-r) -> (0, r^2+3r+2),         (3)
   ```

   and the sum in (1) remains fixed.

Thus ordinary horizontal multiplicity records a conserved collision charge but does not prevent
entry into the critical line. Entry converts cross-mass between distinct zeros at one ordinate
into multiplicity mass at one zero.

## Proof

At a fixed ordinate `gamma`, expand

```text
H_gamma^2
  = sum_(Im rho=gamma) m_rho^2
    + sum_(rho != rho', Im rho=Im rho'=gamma) m_rho m_rho'.
```

After summing over `gamma`, the second term is `O_I`, proving `C_I=D_I+O_I`. Also

```text
D_I-N_I = sum_rho m_rho(m_rho-1)=M_I,
```

which proves (1). Both `O_I` and `M_I` are even because their summands occur as ordered pairs:
`rho != rho'` and `rho' != rho` for `O_I`, and ordered pairs of distinct copies of the same zero
for `M_I`.

If an off-line zero `rho` is present, self-duality supplies the distinct zero
`1-conj(rho)` at the same ordinate, so `O_I>0`. Conversely, two distinct zeros at the same
ordinate cannot both be the unique critical-line point `1/2+i gamma`; hence `O_I>0` implies an
off-line zero. This proves item 2.

For a simple reflected pair, before collision `H_gamma=2`, so `C=4`, `D=2`, and `N=2`; after
collision the unique support point has multiplicity two, so `C=D=4` and `N=2`. This proves (2).
With an existing line multiplicity `r`, the pre-collision values are

```text
C=(r+2)^2,  D=r^2+2,  N=r+2,
```

and the post-collision values are

```text
C=D=(r+2)^2,  N=r+2.
```

Subtraction gives (3).

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The pair-correlation literature already distinguishes diagonal
terms from reflected symmetric-diagonal terms and introduces horizontal multiplicity. Equations
(1)--(3) are the elementary multiset algebra behind that distinction. The decomposition is useful
because it identifies the exact charge that a source theorem must control, but it is not a new
scientific result.

The formal tree already contains the more general parent mechanism that integer winding charge is
homotopy-invariant away from a boundary crossing and can change only at a singular crossing
(`ChargeMotion.lean`). Reformalizing (1)--(3) would add a wrapper around known algebra rather than
scientific content, so no Lean declaration is added for this bridge.

## Consequence for research

An entry-prevention theorem cannot be based on `C_I-N_I` alone: that statistic is unchanged by
collision. It must control `O_I` separately from `M_I`. For zeta, the required new mechanism is a
non-divisor-fed construction from the infinite Euler--Gamma source that either forces `O_I=0` or
forbids the transfer `O_I -> M_I`.


## Lean formalization (stage 3)

The earlier note in this card ("Reformalizing (1)--(3) would add a wrapper ... so no Lean
declaration is added") is superseded: the abstract multiset statement is now formalized, and it is
*not* a wrapper around the existing Xi module — that module carries only the Xi-specific forms of
`C = D + O`, evenness of `O`, and the on-line criterion, and carries neither the multiplicity charge
`M`, the split `(1)`, nor the collision arithmetic `(2)`--`(3)`.

Unconditional and axiom-clean (`propext, Classical.choice, Quot.sound` only) in
`formal/GaloisForLFunctions/HTGeometry/HorizontalChargeTransfer.lean`, namespace
`GaloisForLFunctions.HTGeometry.HorizontalCharge`.  The divisor is a finitely supported
multiplicity function `m : ℂ →₀ ℕ`, so `m ρ ≥ 1` holds on the support by construction and the
degenerate case `r = 0` needs no separate treatment.

```text
horizontalMass m γ       = ∑_{ρ ∈ supp m, Im ρ = γ} m ρ                 (H γ)
divisorMass m            = ∑_{ρ ∈ supp m} m ρ                           (N)
horizontalSquareMass m   = ∑_{γ ∈ Im (supp m)} (horizontalMass m γ)^2   (C)
localSquareMass m        = ∑_{ρ ∈ supp m} (m ρ)^2                       (D)
offLineCharge m          = (C : ℤ) − D                                  (O)
multiplicityCharge m     = (D : ℤ) − N                                  (M)
```

### Item 1 — both charges are nonnegative even integers

```text
offLineCharge_nonneg        : 0 ≤ offLineCharge m
multiplicityCharge_nonneg   : 0 ≤ multiplicityCharge m
even_offLineCharge          : Even (offLineCharge m)
even_multiplicityCharge     : Even (multiplicityCharge m)
```

Nonnegativity of `O` comes from the ordered-pair normal form
`horizontalSquareMass_eq : C = D + crossMass m`, with

```text
crossMass m = ∑_γ ∑_{(ρ,ρ') ∈ offDiag (fibre γ)} m ρ * m ρ'
```

(`offLineCharge_eq_crossMass`), built on the pure-algebra identity
`sq_sum_eq_sum_sq_add_offDiag : (∑ f)^2 = ∑ f^2 + ∑_{offDiag} f p.1 * f p.2`.  Nonnegativity of `M`
uses `m ρ ≤ (m ρ)^2` on the support.  Parity is `n^2 ≡ n (mod 2)` summed fibrewise
(`two_dvd_sq_sub_self`, `two_dvd_horizontalSquareMass_sub_divisorMass`,
`two_dvd_localSquareMass_sub_divisorMass`).

### Item 2 — `O = 0` characterises the critical line

```text
SelfDual m : Prop := ∀ ρ, m (1 - conj ρ) = m ρ

offLineCharge_eq_zero_iff (hdual : SelfDual m) :
  offLineCharge m = 0 ↔ ∀ ρ ∈ m.support, ρ.re = 1 / 2
```

Forward: an off-line `ρ₀` has the *distinct* reflected zero `1 − conj ρ₀` of equal positive
multiplicity at the same ordinate, so its ordered pair contributes to `crossMass`.  Backward: two
support points at one ordinate with `re = 1/2` are equal, so every `offDiag` is empty.

### Item 3 — the split

```text
census_split : (horizontalSquareMass m : ℤ) - divisorMass m
                 = offLineCharge m + multiplicityCharge m
```

### Item 4 — the collision transfer

With `offsetPoint γ a = (1/2 + a) + iγ`,

```text
collisionBefore γ a r = single (offsetPoint γ (-a)) 1 + single (offsetPoint γ a) 1
                          + single (offsetPoint γ 0) r
collisionAfter  γ r   = single (offsetPoint γ 0) (r + 2)
```

and (`a ≠ 0`)

```text
collision_transfer :
  offLineCharge (collisionBefore γ a r)      = 4 * r + 2
∧ multiplicityCharge (collisionBefore γ a r) = r^2 - r
∧ offLineCharge (collisionAfter γ r)         = 0
∧ multiplicityCharge (collisionAfter γ r)    = r^2 + 3 * r + 2
∧ (C - N) before = (C - N) after
```

which is `(3)`, and `collision_transfer_simple` is the `r = 0` case `(2)`:
`(O, M) : (2, 0) → (0, 2)` with `C − N = 2` on both sides.  The supporting single-ordinate lemma is
`horizontalSquareMass_of_single_ordinate : (∀ ρ ∈ supp m, Im ρ = γ) → C = N^2`.

### Relation to the existing Xi module

`RHTower/XiHorizontalCollisionChargeEndpoint.lean` already carries the Xi-window instances of the
census identity, evenness, and the on-line criterion
(`xiStripWindowHorizontalSquareSum_eq_localSquare_add_collisionCharge`,
`xiHorizontalCollisionCharge_even`,
`xiHorizontalCollisionCharge_eq_zero_iff_stripSupport_onLine`), so those were not rebuilt for `Ξ`.

**Stage:** 3-formalized.
