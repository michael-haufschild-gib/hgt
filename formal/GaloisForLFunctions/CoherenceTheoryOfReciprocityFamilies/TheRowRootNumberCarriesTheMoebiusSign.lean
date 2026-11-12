import GaloisForLFunctions.FamilyContinuationTheory.TheSexticGaussSumsAreTwistedMultiplicative
import GaloisForLFunctions.FamilyContinuationTheory.ThePrimeGaussIdentitiesFixTheLocalPhases

/-!
# The root number of a row carries the Möbius sign

The row `u` of the cubic-theta probe carries the `L`-function of the row character
`p ↦ χ_p(u)`, which by sextic reciprocity is the sextic symbol `χ_u` of the modulus `u` up to a
phase of bounded conductor. The dual side of its approximate functional equation is weighted by
the root number, the normalized Gauss sum `g_u^{(1)}(1)` of `χ_u`. The long columns of the floor
bin are therefore sums of the Gauss sums of the row moduli.

For a squarefree `c = π₁ ⋯ π_r` of distinct primary primes `πᵢ ∤ 6`, with
`g_c^{(j)}(1) = Σ_{d mod c} χ_c(d)^j ψ_c(d)` the Gauss sum of `χ_c^j` (`j = 2`: the cubic symbol,
`j = 3`: the quadratic symbol):

`χ_c(4) · g_c^{(1)}(1) · g_c^{(2)}(1) = (−1)^r · c · g_c^{(3)}(1)`   (`rowGauss_product`).

The twisted cross factors `(χ_c(d)χ_d(c))^j` of the three Gauss sums contribute `X¹·X²` on the left
and `X³` on the right, so the defect is multiplicative (`rowGauss_defect_mul`); at a prime it is
`−π` (`rowGauss_product_prime`, the relation `χ(4)G₁G₂ = −πG₃`). Since `|g^{(2)}|² = N(c)`, the
identity says that the sextic root number is `μ(c)` times the conjugate cubic Gauss sum times an
explicit phase:

`g_c^{(1)} = μ(c) · c · \overline{χ_c(4)} · g_c^{(3)} · \overline{g_c^{(2)}} / N(c)`.

So the Möbius sign of the row modulus appears on the dual side of every row, attached to a cubic
Gauss sum. It is the sign of the source identity of the probe (the cube of the composite cubic Gauss
sum is the ideal Möbius value times a phase) and is carried by that cube: the root number is the
square of the normalized cubic Gauss sum times a phase of bounded conductor
(`TheRowRootNumberIsTheSquareOfTheThetaCoefficient`).
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- The left side `χ_c(4) g_c^{(1)}(1) g_c^{(2)}(1)` of the row Gauss identity. -/
def rowGaussProduct (c : O) [NeZero c] : ℂ :=
  sexticSymbol 4 c * sexticGaussPow 1 c 1 * sexticGaussPow 2 c 1

/-- At a prime the composite Gauss sum is the Gauss sum of the power of the residue character. -/
theorem sexticGaussPow_prime (π : O) [NeZero π] [(Ideal.span {π}).IsMaximal]
    (hlam : lambda ∉ Ideal.span {π}) (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)
    {j : ℕ} (hj : j ≠ 0) :
    sexticGaussPow j π 1 =
      gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ j) (principalTraceChar π (NeZero.ne π)) := by
  unfold sexticGaussPow gaussSum
  refine Finset.sum_congr rfl fun d _ => ?_
  have hres : sexticResidue π d = complexSexticChar (Ideal.span {π}) hlam d := by
    unfold sexticResidue
    rw [sexticSymbol_prime π hlam h2 hprim, mk_qrep]
  rw [hres, map_one, one_mul, MulChar.pow_apply' _ hj]

/-- **The row Gauss identity at a prime.** `χ_π(4) G₁ G₂ = −π G₃`. -/
theorem rowGauss_product_prime (π : O) [NeZero π] [(Ideal.span {π}).IsMaximal]
    (hlam : lambda ∉ Ideal.span {π}) (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1) :
    rowGaussProduct π = -ringComplex π * sexticGaussPow 3 π 1 := by
  unfold rowGaussProduct
  rw [sexticGaussPow_prime π hlam h2 hprim one_ne_zero,
    sexticGaussPow_prime π hlam h2 hprim two_ne_zero,
    sexticGaussPow_prime π hlam h2 hprim three_ne_zero, pow_one,
    sexticSymbol_prime π hlam h2 hprim, map_ofNat]
  exact sextic_gauss_product π hlam h2 hprim

/-- **The defect is multiplicative.** If `χ_c(4)g¹_c g²_c = a g³_c` and `χ_d(4)g¹_d g²_d = b g³_d`
for coprime `c, d`, then `χ_{cd}(4) g¹_{cd} g²_{cd} = ab g³_{cd}`: the cross factors `X·X²` and `X³`
cancel. -/
theorem rowGauss_defect_mul (c d : O) [NeZero c] [NeZero d] (hcd : IsCoprime c d) {a b : ℂ}
    (hc : rowGaussProduct c = a * sexticGaussPow 3 c 1)
    (hd : rowGaussProduct d = b * sexticGaussPow 3 d 1) :
    haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
    rowGaussProduct (c * d) = (a * b) * sexticGaussPow 3 (c * d) 1 := by
  haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
  unfold rowGaussProduct at hc hd ⊢
  rw [sexticGaussPow_mul 1 c d hcd 1, sexticGaussPow_mul 2 c d hcd 1,
    sexticGaussPow_mul 3 c d hcd 1, sexticSymbol_mul_denominator]
  set X := sexticSymbol d c * sexticSymbol c d
  calc sexticSymbol 4 c * sexticSymbol 4 d * (X ^ 1 * sexticGaussPow 1 c 1 * sexticGaussPow 1 d 1) *
        (X ^ 2 * sexticGaussPow 2 c 1 * sexticGaussPow 2 d 1)
      = X ^ 3 * (sexticSymbol 4 c * sexticGaussPow 1 c 1 * sexticGaussPow 2 c 1) *
          (sexticSymbol 4 d * sexticGaussPow 1 d 1 * sexticGaussPow 2 d 1) := by ring
    _ = X ^ 3 * (a * sexticGaussPow 3 c 1) * (b * sexticGaussPow 3 d 1) := by rw [hc, hd]
    _ = a * b * (X ^ 3 * sexticGaussPow 3 c 1 * sexticGaussPow 3 d 1) := by ring

/-- The Gauss sums of equal moduli agree, whatever the `NeZero` instances. -/
theorem rowGauss_congr {c c' : O} [NeZero c] [NeZero c'] (h : c = c') :
    rowGaussProduct c = rowGaussProduct c' ∧ sexticGaussPow 3 c 1 = sexticGaussPow 3 c' 1 := by
  subst h
  exact ⟨rfl, rfl⟩

/-- The unit modulus: all three Gauss sums are `1` and `χ_1(4) = 1`. -/
theorem rowGauss_one [NeZero (1 : O)] :
    rowGaussProduct (1 : O) = 1 ∧ sexticGaussPow 3 (1 : O) 1 = 1 := by
  have hg : ∀ j, sexticGaussPow j (1 : O) 1 = 1 := by
    intro j
    unfold sexticGaussPow
    haveI : Subsingleton (O ⧸ Ideal.span {(1 : O)}) := by
      rw [Ideal.span_singleton_one]
      infer_instance
    have hres : sexticResidue 1 0 = 1 := by
      unfold sexticResidue
      exact sexticSymbol_one_denominator _
    rw [Fintype.sum_subsingleton _ 0, mul_zero, AddChar.map_zero_eq_one, hres, one_pow, mul_one]
  refine ⟨?_, hg 3⟩
  unfold rowGaussProduct
  rw [sexticSymbol_one_denominator, hg 1, hg 2]
  ring

/-- **The row Gauss identity.** For a finite set `s` of pairwise coprime nonzero primary primes
`π ∤ 6`, `c = Π_{π ∈ s} π` satisfies `χ_c(4) g_c^{(1)}(1) g_c^{(2)}(1) = (−1)^{|s|} c g_c^{(3)}(1)`:
the Möbius value of the squarefree modulus `c` appears in the product of its sextic and cubic
Gauss sums. -/
theorem rowGauss_product (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
    (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
    (hcop : (s : Set O).Pairwise IsCoprime) [hne : NeZero (∏ π ∈ s, π)] :
    rowGaussProduct (∏ π ∈ s, π) =
      ((-1) ^ s.card * ringComplex (∏ π ∈ s, π)) * sexticGaussPow 3 (∏ π ∈ s, π) 1 := by
  induction s using Finset.induction_on generalizing hne with
  | empty =>
    have h1 : (∏ π ∈ (∅ : Finset O), π) = 1 := Finset.prod_empty
    haveI : NeZero (1 : O) := ⟨one_ne_zero⟩
    obtain ⟨e1, e3⟩ := rowGauss_congr h1
    obtain ⟨o1, o3⟩ := rowGauss_one
    rw [e1, e3, o1, o3, h1, Finset.card_empty, pow_zero, map_one]
    ring
  | insert π t hπt ih =>
    have hπ : π ∈ insert π t := Finset.mem_insert_self π t
    haveI : (Ideal.span {π}).IsMaximal := hmax π hπ
    haveI : NeZero π := ⟨hnz π hπ⟩
    have hsub : ∀ x ∈ t, x ∈ insert π t := fun x hx => Finset.mem_insert_of_mem hx
    have ht0 : ∏ x ∈ t, x ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx => hnz x (hsub x hx)
    haveI : NeZero (∏ x ∈ t, x) := ⟨ht0⟩
    have ih' := ih (fun x hx => hnz x (hsub x hx)) (fun x hx => hmax x (hsub x hx))
      (fun x hx => hlam x (hsub x hx)) (fun x hx => h2 x (hsub x hx))
      (fun x hx => hprim x (hsub x hx)) (hcop.mono (by intro x hx; exact hsub x hx))
    have hcopπ : IsCoprime π (∏ x ∈ t, x) :=
      IsCoprime.prod_right fun x hx => hcop hπ (hsub x hx) (fun h => hπt (h ▸ hx))
    have hp := rowGauss_product_prime π (hlam π hπ) (h2 π hπ) (hprim π hπ)
    have hmul := rowGauss_defect_mul π (∏ x ∈ t, x) hcopπ (a := -ringComplex π)
      (b := (-1) ^ t.card * ringComplex (∏ x ∈ t, x)) hp ih'
    have he : ∏ x ∈ insert π t, x = π * ∏ x ∈ t, x := Finset.prod_insert hπt
    haveI : NeZero (π * ∏ x ∈ t, x) := ⟨mul_ne_zero (hnz π hπ) ht0⟩
    obtain ⟨e1, e3⟩ := rowGauss_congr he
    rw [e1, e3, hmul, he, Finset.card_insert_of_notMem hπt, map_mul, pow_succ]
    ring

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
