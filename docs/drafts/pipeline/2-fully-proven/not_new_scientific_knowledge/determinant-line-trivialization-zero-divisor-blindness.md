# Determinant-line trivialization is blind to the zero divisor

- **ID:** `determinant-line-trivialization-zero-divisor-blindness`
- **Stage:** 2-fully-proven / not-new
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
- [ ] 2 -> 3: no faithful Lean target until the analytic Fredholm determinant line is formalized
- [ ] construct the source-derived nowhere-zero homotopy or one-sided crossing theorem

