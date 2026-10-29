import GaloisForLFunctions.RHTower.HyperellipticRiemannHypothesis
import GaloisForLFunctions.HeckeKreinToeplitz.WeilsIndexIsCountedByTheOuterFrobeniusEigenvalues

/-!
# Stepanov's order over the finite field

The programme's template is Weil's theorem obtained in Stepanov's order: a **producer** yields a
count, and positivity follows. Over `𝔽_q` this chain is complete for the split hyperelliptic curves
`y² = f(x)`, and this module states it in Krein–Langer language.

**The kernel** (`hypTraceKernel`). With `ω` the roots of the reversed `L`-polynomial and `q = |F|`,
`K_f(n) = Σ_ω (ω/√q)^n` on `ℤ`. Over the extension `E` of degree `n`, `√|E| · K_f(n)` is
`|E| − #{y² = f(x)}(E)` (`hypTraceKernel_mul_sqrt_card`): the kernel is the normalized point-count
error on the whole tower of extensions.

**Producer to positivity** (`isPosDefKernel_hypTraceKernel`, `negIndex_hypTraceKernel`). Stepanov's
auxiliary polynomial bounds **both** Legendre parity classes `χ(f(x)) = ±1` over every even-degree
extension; the two classes are the curve and its quadratic twist, so the character sums are bounded
on both sides, the even power sums of `ω²` are `O(q^k)`, and each `|ω| ≤ √q`. The product identity
`|Π ω| = √q^{m−1}` (Gauss sums) forces equality, every normalized root is unitary, and `K_f` is a sum
of unitary characters: index zero.

So over `𝔽_q` the producer acts on both parity classes at once, because the parity twin of the
curve is again a curve. Over `ℤ` one class suffices for the global law
(`riemannHypothesis_iff_oddClass_upper`), but the auxiliary must vanish at that class in a sense
finer than divisibility (`abs_log_lcm_oddPoints_sub_theta_le`).
-/

open Polynomial Finset Complex
open GaloisForLFunctions.HeckeKreinToeplitz GaloisForLFunctions.RHTower.Hyperelliptic

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- The normalized trace kernel of `y² = f`: `n ↦ Σ_ω (ω/√q)^n` on `ℤ`. -/
def hypTraceKernel (f : F[X]) : Multiplicative ℤ → ℂ :=
  fun n => ((lRoots f).map fun ω => valChar (ω / (Real.sqrt (Fintype.card F) : ℂ)) n).sum

theorem hypTraceKernel_eq_sum (f : F[X]) (n : Multiplicative ℤ) :
    hypTraceKernel f n = ∑ i, valChar (rootEnum (lRoots f) i / (Real.sqrt (Fintype.card F) : ℂ)) n := by
  rw [hypTraceKernel]
  conv_lhs => rw [← univ_map_rootEnum (lRoots f), Multiset.map_map]
  rfl

variable (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
  (hodd : Odd f.natDegree)
include hF hsq hsplit hodd

/-- Every normalized root is unitary. -/
theorem norm_div_sqrt_eq_one {ω : ℂ} (hω : ω ∈ lRoots f) :
    ‖ω / (Real.sqrt (Fintype.card F) : ℂ)‖ = 1 := by
  have hq : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hq.le,
    (riemannHypothesis_splitHyperelliptic.{_, 0} hF hsq hsplit hodd).2.1 ω hω, div_self hq.ne']

/-- **Producer to positivity.** The trace kernel of a split hyperelliptic curve is positive
definite. -/
theorem isPosDefKernel_hypTraceKernel : IsPosDefKernel (hypTraceKernel f) := by
  have h := isPosDefKernel_finset_sum (G := Multiplicative ℤ) univ fun i _ =>
    isPosDefKernel_of_unitary (isUnitaryChar_valChar (norm_div_sqrt_eq_one hF hsq hsplit hodd
      (ω := rootEnum (lRoots f) i) (Multiset.mem_toList.mp (List.get_mem _ _))))
  simpa only [← hypTraceKernel_eq_sum] using h

/-- **Weil's theorem as index zero, in Stepanov's order.** -/
theorem negIndex_hypTraceKernel : negIndex (hypTraceKernel f) = 0 :=
  (isPosDefKernel_hypTraceKernel hF hsq hsplit hodd).negIndex_eq_zero

/-- **The kernel is the normalized count error.** Over an extension `E` of degree `n`,
`√|E| · K_f(n) = |E| − #{(x, y) ∈ E² : y² = f(x)}`. -/
theorem hypTraceKernel_mul_sqrt_card (E : Type*) [Field E] [Fintype E] [Algebra F E] :
    hypTraceKernel f (Multiplicative.ofAdd (Module.finrank F E : ℤ)) *
        (Real.sqrt (Fintype.card E) : ℂ) =
      Fintype.card E - ((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℂ) := by
  obtain ⟨-, hnorm, hsum⟩ := riemannHypothesis_splitHyperelliptic hF hsq hsplit hodd
  set n := Module.finrank F E
  have hq : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hqC : (Real.sqrt (Fintype.card F) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs : Real.sqrt ((Fintype.card F : ℝ) ^ n) = Real.sqrt (Fintype.card F) ^ n := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hsqrtE : (Real.sqrt (Fintype.card E) : ℂ) = (Real.sqrt (Fintype.card F) : ℂ) ^ n := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E), Nat.cast_pow, hs]
    push_cast; rfl
  -- the kernel at `n` is `Σ ω^n / √q^n`
  have hK : hypTraceKernel f (Multiplicative.ofAdd (n : ℤ)) * (Real.sqrt (Fintype.card F) : ℂ) ^ n =
      ((lRoots f).map (· ^ n)).sum := by
    rw [hypTraceKernel, Multiset.sum_map_mul_right.symm]
    congr 1
    refine Multiset.map_congr rfl fun ω hω => ?_
    have hω0 : ω / (Real.sqrt (Fintype.card F) : ℂ) ≠ 0 := by
      intro h0
      have := norm_div_sqrt_eq_one hF hsq hsplit hodd hω
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    simp only [valChar, MonoidHom.coe_mk, OneHom.coe_mk, if_neg hω0, toAdd_ofAdd, zpow_natCast,
      div_pow]
    field_simp
  -- the count is `|E| + Σ_x χ(f(x))`, the character sum is `−Σ ω^n`
  have hcount := card_points_eq (E := E) (by rwa [← Algebra.ringChar_eq F E]) (f.map (algebraMap F E))
  simp only [eval_map, ← aeval_def] at hcount
  have hcountC := congrArg (fun z : ℤ => (z : ℂ)) hcount
  push_cast at hcountC
  have he : ((lRoots f).map (· ^ n)).sum = -extHyp (E := E) f := by rw [hsum E, neg_neg]
  rw [hsqrtE, hK, hcountC, he]
  unfold extHyp
  ring

/-- **Stepanov's order over `𝔽_q`.** For `y² = f(x)`, `f` split, squarefree, of odd degree, in odd
characteristic: the normalized point-count errors over all extensions are the values of one kernel on
`ℤ`, and that kernel has no negative square. -/
theorem stepanov_order_hyperelliptic :
    negIndex (hypTraceKernel f) = 0 ∧
      ∀ (E : Type*) [Field E] [Fintype E] [Algebra F E],
        hypTraceKernel f (Multiplicative.ofAdd (Module.finrank F E : ℤ)) *
            (Real.sqrt (Fintype.card E) : ℂ) =
          Fintype.card E - ((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℂ) :=
  ⟨negIndex_hypTraceKernel hF hsq hsplit hodd, fun E _ _ _ =>
    hypTraceKernel_mul_sqrt_card hF hsq hsplit hodd E⟩

end GaloisForLFunctions.ArithmeticKreinLangerTheory

open GaloisForLFunctions.ArithmeticKreinLangerTheory in
#print axioms stepanov_order_hyperelliptic
