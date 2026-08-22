# Artin two-generator associativity for alternative algebras

- **ID:** `artin-two-generator-associativity-alternative-algebras`
- **Stage:** `3-formalized/not_new_scientific_knowledge`
- **Type:** infrastructure theorem
- **Source:** R. D. Schafer, *An Introduction to Nonassociative Algebras*, Theorem 3.1, pp. 29--30.
- **Needed by:** arXiv:2605.07183 Lemma 8.4 equation (8.6), then all slice-plane and power-associative results.

## Audit

- **[CORPUS]** `formal_tools.py research "Artin alternative algebra two generator associative subalgebra" --scan` found no alternative-algebra or diassociativity implementation.
- **[MATHLIB]** Source search found no `IsAlternative`, Artin, diassociative, or two-generator-alternative theorem.
- **[LOCAL]** `tmp/jordan/Alternative.lean` contains alternation, Teichmüller, and one Moufang identity but not Artin's theorem.  The project-owned `HTGeometry/Octonion/Alternative.lean` has integrated and extended those reusable identities, including the reciprocal Moufang identity and Schafer's associator identity (3.7).

## Dependency-closed paper proof

Let `p,q,r` be bracketed words in two fixed generators, and let their degrees be the respective word lengths.  Prove `[p,q,r]=0` by strong induction on the total degree `n`.

For `n < 3` the result is vacuous.  At total degree `n`, the induction hypothesis makes every proper subword associative, hence each of `p,q,r` can be written beginning with its first letter.  Two of these words begin with the same generator `x`; by alternation of the associator, arrange `q = x q'` and `r = x r'` when both have degree greater than one.  Schafer's linearized reciprocal Moufang identity gives

```text
[p, x q', x r'] = -[x r', q', p]
                  = [x r', p q', x] + [x r', x, q']p + [x r', p, q']x
                  = -[p q', x r', x]
                  = [p q', x, r']x = 0,
```

where each final associator has smaller total degree.  If exactly one of `q,r` has degree greater than one, the reciprocal Moufang identity directly reduces to a smaller associator; if neither does, right alternativity gives zero.  Trilinearity of the associator extends this from words to the unital real subalgebra they generate.  Thus that subalgebra is associative.

## Lean plan

1. Introduce syntax for bracketed two-generator words, evaluation, degree, initial letter, and rebracketing under the strong induction hypothesis.
2. Formalize Schafer's degree induction using `IsAlternative.associator_right_mul_left`, `teichmuller`, alternation, and right alternativity.
3. Close the real-linear/additive span under multiplication and lift the word theorem by trilinearity.
4. Instantiate at `RealOctonion`; define the two-generator subalgebra and prove paper equation (8.6) without an external premise.

## Gates

- [x] Corpus and Mathlib duplication audit
- [x] Source proof extracted and reduced to existing alternative identities
- [x] Reciprocal Moufang / associator identities (3.7)--(3.8) formalized
- [x] Word-level strong induction theorem
- [x] Real-linear generated-subalgebra closure and associativity lift
- [x] Lemma 8.4 equation (8.6) instantiated and audited

## Formalization result

`HTGeometry/Octonion/Artin.lean` proves `ArtinWord.all_words_associate` by the stated strong induction.  `HTGeometry/Octonion/GeneratedSubalgebra.lean` takes the real span of bracketed words and scalar elements, proves its product closure, and lifts vanishing of the associator over three nested span inductions.  The resulting theorem `associator_eq_zero_of_mem_generatedSubmodule` has no premises beyond its universal variables and membership in the definitionally specified generated carrier.  It yields the correction-free form of paper Lemma 8.4 on that carrier.

Targeted source checks and targeted builds pass; `#print axioms` for the closure, associativity, and (8.6) theorems reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
