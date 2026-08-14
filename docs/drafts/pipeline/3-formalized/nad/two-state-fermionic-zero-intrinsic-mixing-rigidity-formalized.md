# Two-state fermionic zero intrinsic mixing rigidity — formalized

- **ID:** `two-state-fermionic-zero-intrinsic-mixing-rigidity-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `two-state-fermionic-zero-intrinsic-mixing-rigidity.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/DecomposableTensorRigidity.lean` | the classification-free algebraic core of the product-grid gauge-rigidity lemma, both branches |
| `HTGeometry/FermionicFactorialTraceBound.lean` | the identity-zero twist, the componentwise antisymmetrizer, and the factorial trace gain used by the identity-zero frame gate |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`
(`criticalHorizonSegreTensor_sum_smul` needs only `propext`, `Quot.sound`).

- `criticalHorizonSegreTensor_eq_zero_iff` — a decomposable tensor vanishes exactly when one factor
  does;
- `criticalHorizonSegreTensor_rigidity` and `criticalHorizonSegreTensor_eq_rigidity` — **equality of
  two nonzero decomposable tensor lines forces equality of each factor up to reciprocal scalars**.
  This is the step the product-grid gauge-rigidity lemma leans on three separate times, and it is
  proved with no input from the de Leeuw–Posch classification;
- `criticalHorizonSegreTensor_left_line`, `criticalHorizonSegreTensor_right_line`,
  `criticalHorizonSegreTensor_left_cancel`, `criticalHorizonSegreTensor_right_cancel` — the
  one-sided forms used branch by branch;
- `criticalHorizonSegreTensor_add_left`, `criticalHorizonSegreTensor_smul_left`,
  `criticalHorizonSegreTensor_add_right`, `criticalHorizonSegreTensor_smul_right`,
  `criticalHorizonSegreTensor_sum_smul` — bilinearity and the finite-sum expansion of the Segre
  embedding, which is what turns a spectral multiplicity pattern into a product grid.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/DecomposableTensorRigidity.lean
```

## What closed last

The gauge-rigidity lemma's algebraic core, stated so that it needs no classification input.  The
card's own Lean boundary had ruled out encoding the external complete classification as a
hypothesis, on the grounds that this would not be an unconditional formalization; the way past that
was to isolate the part of the argument that is classification-free — the rigidity of decomposable
tensor lines — and prove it outright over an arbitrary field.

## Boundary

The **global** theorem is not formalized: it uses an external complete classification of the
two-state solutions whose many analytic matrix families are not in the project, exactly as the
card's Lean boundary states.  The remaining paper gates — an independent specialist audit of the
classification-equivalence closure, an expert novelty assessment of the full sixteen-entry
corollary, a classification-free proof of the global statement, and a uniformly `exp(O(n))`
conditioned identity-zero braid intertwiner — are external audits and onward research targets, not
formalization gates for the surface certified above.
