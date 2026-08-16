# Determinant-line trivialization is blind to the zero divisor

- **ID:** `determinant-line-trivialization-zero-divisor-blindness`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper) / NO-GO WITH POSITIVE SUCCESSOR
- **Source:** `ccm-weierstrass-stabilized-square-evans-line-law.md` and the complete-corpus
  determinant-line audit
- **Statement:** Triviality or null-homotopy of a determinant line over a spectral interval places
  no restriction on the zero divisor of its Evans section; excluding spectral crossings requires
  a source-defined homotopy through nowhere-zero sections, or equivalent nonvanishing and
  one-sided crossing data.

## Goal

Decide whether the already constructed source-normalized CCM determinant line can prove RH by a
topological no-first-crossing argument without first proving an analytic sign or nonvanishing
theorem.

## Theorem

Let `I` be a real interval, let `L -> I` be a complex line bundle, and let `E` be a continuous,
smooth, or real-analytic section in the corresponding category.

1. The line `L` is trivial because `I` is contractible.
2. After choosing a trivialization, `E` is a scalar function `e : I -> C`.
3. Every prescribed finite interior divisor occurs for a section of the trivial line.  For points
   `lambda_j` and positive multiplicities `m_j`, the real-analytic section

   ```text
   e(lambda) = product_j (lambda-lambda_j)^(m_j)
   ```

   has exactly that divisor on a sufficiently small interval containing the points and no other
   zeros there.
4. Consequently, a trivialization or a null-homotopy of `L` does not imply that `E` is nonzero and
   does not exclude a first spectral crossing.
5. A homotopy from `E` to a nonzero reference section through nowhere-zero sections exists only if
   `E` itself is nowhere zero.  For an Evans section this is precisely the desired spectral
   nonvanishing statement, not a weaker topological input.

For a two-parameter self-adjoint Fredholm family, boundary winding counts signed crossings.  Zero
winding alone permits cancelling positive and negative crossings.  It computes the total negative
index only after an independent one-sided crossing-orientation or monotonicity theorem is supplied.

## Proof

Contractibility of `I` gives a nowhere-zero frame of `L`, proving (1)--(2).  The displayed
polynomial proves (3), and (4) follows immediately.  If a homotopy consists entirely of
nowhere-zero sections, its initial section is nowhere zero, proving the necessary part of (5); the
converse on an interval follows by trivializing and homotoping inside `C*` componentwise after
choosing a continuous logarithm.  The winding statement is the standard oriented-crossing formula
for determinant sections: opposite crossing signs cancel in the integer even though both zeros
remain.

## Positive source theorem

The determinant-line route remains live only in either of the following strictly stronger forms.

```text
source-normalized Evans section
  + explicit homotopy through nowhere-zero sections on lambda <= 0
  -> empty nonpositive zero divisor,
```

or

```text
source boundary nonvanishing
  + source-derived one-sided crossing orientation or aperture monotonicity
  + zero boundary winding from the initial positive chamber
  -> zero negative Morse charge
  -> RH.
```

Thus the positive object is not a null-homotopy of the line.  It is a null-homotopy in the
complement of the zero section, or an index-faithful oriented crossing law.  This formulation keeps
the complete negative index and states exactly what a source construction must provide.

## Scope

This is standard determinant-line topology and spectral-flow theory, so it is not new scientific
knowledge.  It retires only the line-triviality shortcut.  The source-normalized Evans section and
the possibility of a genuinely arithmetic zero-avoidance or one-sided-orientation theorem remain
live.  The analytic Fredholm family is absent from Lean, so an abstract wrapper would not
formalize the project object and is not added.

## Gates

- [x] 0 -> 1: determinant-line null-homotopy claim isolated
- [x] 1 -> 2: complete proof and arbitrary-divisor counterexample supplied
- [x] positive successor stated as source zero-avoidance or index-faithful orientation
- [x] 2 -> 3: `RHTower/DeterminantLineDivisorBlindness.lean` — the no-go content is Lean-proved directly for the trivial line, which is what a no-go needs
- [ ] construct the source-derived nowhere-zero homotopy or one-sided crossing theorem

## 2026-08-16 Lean closure

`RHTower/DeterminantLineDivisorBlindness.lean` proves the decisive content unconditionally.

- `exists_section_with_prescribed_divisor` is clause 3 in exact form: for any finite family of
  points and positive multiplicities there is a continuous section of the trivial line — the
  polynomial section `prod_j (lambda - lambda_j)^(m_j)` — whose zero set is exactly the prescribed
  points and whose root multiset (`divisorSectionPoly_roots`) is exactly the prescribed divisor.
  Clause 4 follows immediately.
- `nonvanishing_of_nowhereZero_homotopy` is the necessary half of clause 5: if every stage of a
  homotopy is nowhere zero, the initial section is nowhere zero, so a nowhere-zero homotopy is not
  a weaker topological input than the nonvanishing statement itself.
- `crossingExample_signs` is the winding remark: `lambda^2 - 1` vanishes at two points whose
  crossing derivatives have opposite signs and sum to zero, so a zero signed count coexists with
  two surviving zeros.

**Scope.**  Clauses 1--2 (a complex line bundle over an interval is trivial, so a section becomes a
scalar function) are classical bundle theory and are used only to reduce to the trivialized
picture.  The Lean theorems are stated directly for the trivial line, which is exactly what the
no-go requires: exhibiting sections of the trivial line with arbitrary divisors shows that
triviality places no restriction.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
