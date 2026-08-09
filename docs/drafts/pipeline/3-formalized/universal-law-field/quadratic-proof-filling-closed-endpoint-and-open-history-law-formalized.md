# Quadratic proof filling, closed endpoint, open history — Lean certification

- **ID:** ULF-FILL-1
- **Paper card:**
  `quadratic-proof-filling-closed-endpoint-and-open-history-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveQuadraticFilling`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## New corpus infrastructure

Mathlib has no van Kampen area, no Dehn function, and no Heisenberg group; all three layers are
built here.

- `Heis` — the integer Heisenberg group `ℤ³` with `(x,y,z)·(x',y',z') = (x+x', y+y', z+z'+x y')`,
  with its `Group` instance, its central subgroup `Heis.center`, and `Heis.conj_center`,
  `Heis.center_mul`, `Heis.center_injective`;
- `cellWord`, `IsFilling`, `Fillable`, `area` — van Kampen fillings of a word by conjugates of the
  relator and its inverse, and the minimal cell count, with closure under concatenation
  (`isFilling_append`), conjugation (`isFilling_conj`), and inversion (`isFilling_inv`);
- `NoCancel`, `reduce_eq_self_of_isChain`, `isChain_replicate_append` — a reduced-word criterion
  from `List.IsChain`, used to compute reduced lengths of explicit block words.

## Certified declarations

### Theorem 2.1 — endpoint return with quadratic minimal proof history

- **Endpoint.**  `nullWord_mem_normalClosure` places `w n = aⁿ bⁿ a⁻ⁿ b⁻ⁿ` in the normal closure of
  the relator, so `nullWord_eq_one_in_quotient` proves its class is `1` in
  `FreeGroup (Fin 2) ⧸ normalClosure {[a,b]}`, the presented group `⟨a,b | [a,b]⟩`.
  `abelLift_nullWord` gives the same conclusion directly in `ℤ²`.
- **Length.**  `mk_nullList` identifies `w n` with the explicit block word
  `aⁿ bⁿ a⁻ⁿ b⁻ⁿ`, `isChain_nullList` proves that word has no adjacent cancelling pair, and
  `reduce_eq_self_of_isChain` therefore identifies it with the reduced word.  Hence
  `length_nullWord : (nullWord n).toWord.length = 4 * n`.
- **Upper bound.**  `comm_mul_left` and `comm_mul_right` are the two commutator expansions
  (proved by the `group` normalizer).  `fillable_comm_genA_genB_pow` fills `[a, bᵐ]` with `m`
  cells, and `fillable_comm_pow` iterates it into the `n × m` grid, giving
  `fillable_nullWord : Fillable (n ^ 2) (nullWord n)`.
- **Lower bound.**  `heisLift` is the Heisenberg representation; `heisLift_relator` sends the
  relator to the central generator and `heisLift_nullWord` sends `w n` to the central element of
  exponent `n²`.  `heisLift_cellWord` shows every filling cell maps to a central element of
  exponent `±1` — conjugation is invisible because the target is central — so
  `heisLift_of_isFilling` bounds the total exponent of a `k`-cell filling by `k` in absolute value.
- **Conclusion.**  `area_nullWord : area (nullWord n) = n ^ 2`.

### Corollary 2.2 — positive filling cost forgets orientation

`fillable_inv_iff` and `area_inv` prove `area w⁻¹ = area w` for every word, hence
`area_nullWord_inv : area (nullWord n)⁻¹ = n ^ 2`.

### Capstone

`quadratic_filling_law` bundles all five conclusions: trivial class in the presented group, trivial
image in `ℤ²`, reduced length `4n`, area `n²`, and area `n²` for the reversed word.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveQuadraticFilling.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveQuadraticFilling
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` on the area theorem, the length theorem, the
orientation blindness, both endpoint statements, and the capstone reports only `propext`,
`Classical.choice`, and `Quot.sound` (the `ℤ²` endpoint needs only `propext` and `Quot.sound`).  No
project axiom, placeholder, hypothesis interface, or unresolved theorem premise is used.

## Exact field consequence

The endpoint observer is blind to a diverging two-dimensional proof history: identical trivial
endpoints, linear boundary length, and quadratic minimal filling volume coexist in one elementary
family.  Complexity here is minimal filling volume rather than path length, and the passage from an
oriented filling current to unsigned volume is a genuine quotient — the reversed word costs the
same.
