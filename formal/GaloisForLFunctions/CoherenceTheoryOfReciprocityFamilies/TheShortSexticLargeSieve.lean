import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheShortSexticGramIsDiagonal
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheReflectedGramIsTwistedByTheRowRootNumbers

/-!
# Unrestricted fifth-power conjugation and the smooth short sextic large sieve over `ℤ[ω]`

`conj_sexticSymbol_eq_pow_five` identifies `\overline{χ_c(x)} = χ_c(x)⁵` at residues `x` prime to `c`,
whereas a smooth lattice sum over `n ∈ ℤ²` evaluates `χ_c` at all `x = n₀ + n₁ ω ∈ ℤ[ω]`, including
elements sharing prime factors with `c`. Extending the fifth-power conjugation law and unit-disk
bound to **all** `x ∈ ℤ[ω]` for squarefree products of primary primes `π ∤ 6` connects Hermitian `L²`
lattice norms directly to `norm_gramEntry_le` with zero coprimality sieving:

* **Unrestricted fifth-power conjugation and unit-disk bound (`conj_sexticSymbol_prod_eq_pow_five`,
  `norm_sexticSymbol_prod_le_one`).** For every finite set `s` of primary primes `π ∤ 6` and every
  `x ∈ O`, `conj (sexticSymbol x (∏ π ∈ s, π)) = sexticSymbol x (∏ π ∈ s, π) ^ 5` and
  `‖sexticSymbol x (∏ π ∈ s, π)‖ ≤ 1`.
* **Hermitian symmetry of `sexticGramEntry` (`conj_sexticGramEntry`, `norm_sexticGramEntry_symm`).**
  For any real-valued Schwartz profile `f`, `conj (G(u₁, u₂)) = G(u₂, u₁)` and
  `‖G(u₁, u₂)‖ = ‖G(u₂, u₁)‖`.
* **Smooth Schur sextic large sieve (`short_sextic_large_sieve_rowwise`,
  `short_sextic_large_sieve`).** For any nonnegative real Schwartz profile `f`, linear isomorphism
  `B`, finite family `(s_i)_{i ∈ F}` of primary prime sets (`π ∤ 6`), and complex weights `c_i`,
  `∑_n Re f(Bn) ‖∑_{i ∈ F} c_i χ_{u_i}(n)‖² ≤ ∑_{i ∈ F} ‖c_i‖² (∑_n Re f(Bn) + ∑_{j ≠ i} ‖G(u_i, u_j)‖)`,
  where each off-diagonal entry `‖G(u_i, u_j)‖` decays rapidly below the row scale by
  `norm_gramEntry_le`.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate FourierTransform

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open HTGeometry HTGeometry.IntegerLatticePoisson MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.Eisenstein.Coordinates
  FamilyContinuationTheory

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Z" => Fin 2 → ℤ

/-! ### Part 1: Unrestricted fifth-power conjugation and unit-disk bound -/

/-- Predicates characterizing a finite set `s` of primary primes `π ∤ 6` in `O = ℤ[ω]`. -/
structure IsGoodPrimeSet (s : Finset O) : Prop where
  ne_zero : ∀ π ∈ s, π ≠ 0
  isMaximal : ∀ π ∈ s, (Ideal.span {π}).IsMaximal
  not_mem_lambda : ∀ π ∈ s, lambda ∉ Ideal.span {π}
  not_mem_two : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}
  primary : ∀ π ∈ s, lambda ^ 2 ∣ π - 1

theorem IsGoodPrimeSet.subset {s t : Finset O} (ht : IsGoodPrimeSet t) (hst : s ⊆ t) :
    IsGoodPrimeSet s where
  ne_zero π hπ := ht.ne_zero π (hst hπ)
  isMaximal π hπ := ht.isMaximal π (hst hπ)
  not_mem_lambda π hπ := ht.not_mem_lambda π (hst hπ)
  not_mem_two π hπ := ht.not_mem_two π (hst hπ)
  primary π hπ := ht.primary π (hst hπ)

private lemma sexticSymbol_eq_zero_of_not_isCoprime_prime (π : O) [NeZero π]
    [hmax : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
    (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1) {x : O}
    (hnot : ¬ IsCoprime x π) : sexticSymbol x π = 0 := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have hmk0 : Ideal.Quotient.mk (Ideal.span {π}) x = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (Ideal.span {π}) x)⁻¹
    have hmul : Ideal.Quotient.mk (Ideal.span {π}) (x * y) = 1 := by
      rw [map_mul, hy, mul_inv_cancel₀ hne]
    have hdvd : π ∣ x * y - 1 := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hmul)
    obtain ⟨z, hz⟩ := hdvd
    refine hnot ⟨y, -z, ?_⟩
    linear_combination hz
  rw [sexticSymbol_prime π hlam h2 hprim, hmk0, MulChar.map_nonunit _ not_isUnit_zero]

private lemma conj_and_norm_sexticSymbol_prime (π : O) [NeZero π]
    [(Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
    (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1) (x : O) :
    conj (sexticSymbol x π) = sexticSymbol x π ^ 5 ∧ ‖sexticSymbol x π‖ ≤ 1 := by
  by_cases hcop : IsCoprime x π
  · have hπ2 : IsCoprime π 2 := isCoprime_two_of_prime (prime_of_isMaximal_span π) h2
    exact ⟨conj_sexticSymbol_eq_pow_five (NeZero.ne π) hprim hπ2 hcop,
      (norm_sexticSymbol_eq_one (NeZero.ne π) hprim hπ2 hcop).le⟩
  · have hz := sexticSymbol_eq_zero_of_not_isCoprime_prime π hlam h2 hprim hcop
    rw [hz, map_zero, zero_pow (by decide), norm_zero]
    exact ⟨rfl, zero_le_one⟩

/-- **Unrestricted fifth-power conjugation law.** For every `x ∈ O` (coprime or not) and every
finite set `s` of primary primes `π ∤ 6`, `\overline{χ_{∏_s π}(x)} = χ_{∏_s π}(x)⁵`. -/
theorem conj_sexticSymbol_prod_eq_pow_five {s : Finset O} (hs : IsGoodPrimeSet s) (x : O) :
    conj (sexticSymbol x (∏ π ∈ s, π)) = sexticSymbol x (∏ π ∈ s, π) ^ 5 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, sexticSymbol_one_denominator, map_one, one_pow]
  | insert π t hπt ih =>
    have hπ : π ∈ insert π t := Finset.mem_insert_self π t
    haveI : NeZero π := ⟨hs.ne_zero π hπ⟩
    haveI : (Ideal.span {π}).IsMaximal := hs.isMaximal π hπ
    have hst : IsGoodPrimeSet t := hs.subset (Finset.subset_insert π t)
    have h1 := (conj_and_norm_sexticSymbol_prime π (hs.not_mem_lambda π hπ)
      (hs.not_mem_two π hπ) (hs.primary π hπ) x).1
    rw [Finset.prod_insert hπt, sexticSymbol_mul_denominator, map_mul, h1, ih hst, mul_pow]

/-- **Unrestricted unit-disk bound.** For every `x ∈ O` and every finite set `s` of primary primes
`π ∤ 6`, `‖sexticSymbol x (∏ π ∈ s, π)‖ ≤ 1`. -/
theorem norm_sexticSymbol_prod_le_one {s : Finset O} (hs : IsGoodPrimeSet s) (x : O) :
    ‖sexticSymbol x (∏ π ∈ s, π)‖ ≤ 1 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, sexticSymbol_one_denominator, norm_one]
  | insert π t hπt ih =>
    have hπ : π ∈ insert π t := Finset.mem_insert_self π t
    haveI : NeZero π := ⟨hs.ne_zero π hπ⟩
    haveI : (Ideal.span {π}).IsMaximal := hs.isMaximal π hπ
    have hst : IsGoodPrimeSet t := hs.subset (Finset.subset_insert π t)
    have h1 := (conj_and_norm_sexticSymbol_prime π (hs.not_mem_lambda π hπ)
      (hs.not_mem_two π hπ) (hs.primary π hπ) x).2
    rw [Finset.prod_insert hπt, sexticSymbol_mul_denominator, norm_mul]
    exact mul_le_one₀ h1 (norm_nonneg _) (ih hst)

/-! ### Part 2: Hermitian symmetry of the smooth sextic Gram matrix -/

/-- Smooth sextic Gram entry `G(u₁, u₂) = ∑_{n ∈ ℤ²} χ_{u₁}(n) χ_{u₂}(n)⁵ f(Bn)`. -/
def sexticGramEntry (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (u₁ u₂ : O) : ℂ :=
  ∑' n : Z, (sexticSymbol (eval (n 0) (n 1)) u₁ * sexticSymbol (eval (n 0) (n 1)) u₂ ^ 5) *
    f (B (euclideanIntegerPoint n))

private lemma summable_sexticGramTerm (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) {s₁ s₂ : Finset O}
    (hs₁ : IsGoodPrimeSet s₁) (hs₂ : IsGoodPrimeSet s₂) :
    Summable fun n : Z =>
      (sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s₁, π) *
          sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s₂, π) ^ 5) *
        f (B (euclideanIntegerPoint n)) := by
  refine Summable.of_norm_bounded (summable_norm_affine_lattice f B 0) fun n => ?_
  rw [norm_mul, norm_mul, norm_pow, add_zero]
  have h1 := norm_sexticSymbol_prod_le_one hs₁ (eval (n 0) (n 1))
  have h2 : ‖sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s₂, π)‖ ^ 5 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_sexticSymbol_prod_le_one hs₂ _)
  calc ‖sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s₁, π)‖ *
        ‖sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s₂, π)‖ ^ 5 * ‖f (B (euclideanIntegerPoint n))‖
      ≤ 1 * ‖f (B (euclideanIntegerPoint n))‖ :=
        mul_le_mul_of_nonneg_right (mul_le_one₀ h1 (by positivity) h2) (norm_nonneg _)
    _ = ‖f (B (euclideanIntegerPoint n))‖ := one_mul _

/-- For any real-valued Schwartz profile `f`, `sexticGramEntry` is Hermitian across good prime
products: `\overline{G(u₁, u₂)} = G(u₂, u₁)`. -/
theorem conj_sexticGramEntry (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E)
    (hf_real : ∀ v : E, f v = ((f v).re : ℂ)) {s₁ s₂ : Finset O}
    (hs₁ : IsGoodPrimeSet s₁) (hs₂ : IsGoodPrimeSet s₂) :
    conj (sexticGramEntry f B (∏ π ∈ s₁, π) (∏ π ∈ s₂, π)) =
      sexticGramEntry f B (∏ π ∈ s₂, π) (∏ π ∈ s₁, π) := by
  unfold sexticGramEntry
  rw [← Complex.conjCLE_apply, Complex.conjCLE.map_tsum]
  congr 1
  funext n
  rw [Complex.conjCLE_apply, map_mul, map_mul,
    conj_sexticSymbol_prod_eq_pow_five hs₁ (eval (n 0) (n 1)),
    ← conj_sexticSymbol_prod_eq_pow_five hs₂ (eval (n 0) (n 1)), Complex.conj_conj,
    hf_real (B (euclideanIntegerPoint n)), Complex.conj_ofReal]
  ring

/-- Symmetry of off-diagonal Gram norms for real-valued Schwartz profiles. -/
theorem norm_sexticGramEntry_symm (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E)
    (hf_real : ∀ v : E, f v = ((f v).re : ℂ)) {s₁ s₂ : Finset O}
    (hs₁ : IsGoodPrimeSet s₁) (hs₂ : IsGoodPrimeSet s₂) :
    ‖sexticGramEntry f B (∏ π ∈ s₁, π) (∏ π ∈ s₂, π)‖ =
      ‖sexticGramEntry f B (∏ π ∈ s₂, π) (∏ π ∈ s₁, π)‖ := by
  rw [← conj_sexticGramEntry f B hf_real hs₁ hs₂, RCLike.norm_conj]

/-! ### Part 3: Smooth Schur sextic large sieve over `ℤ[ω]` -/

/-- **Row-wise smooth Schur sextic large sieve over `ℤ[ω]`.** For any real nonnegative Schwartz
profile `f`, lattice map `B`, finite family `F` of good prime sets `s i`, and weights `c i ∈ ℂ`:
`∑_n Re f(Bn) ‖∑_{i ∈ F} c_i χ_{u_i}(n)‖² ≤ ∑_{i ∈ F} ‖c_i‖² (∑_n Re f(Bn) + ∑_{j ≠ i} ‖G(u_i, u_j)‖)`. -/
theorem short_sextic_large_sieve_rowwise {I : Type*} [DecidableEq I]
    (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E)
    (hf_real : ∀ v : E, f v = ((f v).re : ℂ)) (hf_nonneg : ∀ v : E, 0 ≤ (f v).re)
    (F : Finset I) (s : I → Finset O) (hs : ∀ i ∈ F, IsGoodPrimeSet (s i)) (c : I → ℂ) :
    (∑' n : Z, (f (B (euclideanIntegerPoint n))).re *
        ‖∑ i ∈ F, c i * sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π)‖ ^ 2) ≤
      ∑ i ∈ F, ‖c i‖ ^ 2 *
        ((∑' n : Z, (f (B (euclideanIntegerPoint n))).re) +
          ∑ j ∈ F.erase i, ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) := by
  have hsum_w : Summable fun n : Z => (f (B (euclideanIntegerPoint n))).re := by
    refine Summable.of_nonneg_of_le (fun n => hf_nonneg _) (fun n => ?_)
      (summable_norm_affine_lattice f B 0)
    rw [add_zero]
    exact Complex.re_le_norm _
  let term (i j : I) (n : Z) : ℝ :=
    ((c i * conj (c j)) *
      ((sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π) *
          sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s j, π) ^ 5) *
        f (B (euclideanIntegerPoint n)))).re
  have hsum_term : ∀ i ∈ F, ∀ j ∈ F, Summable (term i j) := by
    intro i hi j hj
    exact Complex.reCLM.summable
      ((summable_sexticGramTerm f B (hs i hi) (hs j hj)).mul_left (c i * conj (c j)))
  have hpt : ∀ n : Z,
      (f (B (euclideanIntegerPoint n))).re *
          ‖∑ i ∈ F, c i * sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π)‖ ^ 2 =
        ∑ i ∈ F, ∑ j ∈ F, term i j n := by
    intro n
    set z : ℂ := ∑ i ∈ F, c i * sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π)
    have hsq : ‖z‖ ^ 2 = (z * conj z).re := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [hsq]
    have hprod : ((f (B (euclideanIntegerPoint n))).re : ℂ) * (z * conj z) =
        ∑ i ∈ F, ∑ j ∈ F, (c i * conj (c j)) *
          ((sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π) *
              sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s j, π) ^ 5) *
            f (B (euclideanIntegerPoint n))) := by
      rw [← hf_real (B (euclideanIntegerPoint n))]
      dsimp only [z]
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [map_mul, conj_sexticSymbol_prod_eq_pow_five (hs j hj)]
      ring
    have hre := congrArg Complex.re hprod
    rw [Complex.re_ofReal_mul] at hre
    rw [hre, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
  simp_rw [hpt]
  have hsum_inner : ∀ i ∈ F, Summable fun n : Z => ∑ j ∈ F, term i j n :=
    fun i hi => summable_sum fun j hj => hsum_term i hi j hj
  rw [Summable.tsum_finsetSum hsum_inner]
  have hrow_split : ∀ i ∈ F,
      (∑' n : Z, ∑ j ∈ F, term i j n) ≤
        ‖c i‖ ^ 2 * (∑' n : Z, (f (B (euclideanIntegerPoint n))).re) +
          ∑ j ∈ F.erase i, ‖c i‖ * ‖c j‖ *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ := by
    intro i hi
    rw [Summable.tsum_finsetSum fun j hj => hsum_term i hi j hj, ← Finset.add_sum_erase F _ hi]
    have hdiag : (∑' n : Z, term i i n) ≤
        ‖c i‖ ^ 2 * ∑' n : Z, (f (B (euclideanIntegerPoint n))).re := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun n => ?_) (hsum_term i hi i hi) (hsum_w.mul_left _)
      dsimp only [term]
      rw [← conj_sexticSymbol_prod_eq_pow_five (hs i hi), hf_real (B (euclideanIntegerPoint n))]
      have hcc : (c i * conj (c i)) *
          ((sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π) *
              conj (sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π))) *
            ((f (B (euclideanIntegerPoint n))).re : ℂ)) =
          ((‖c i‖ ^ 2 * ‖sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π)‖ ^ 2 *
            (f (B (euclideanIntegerPoint n))).re : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq]
        push_cast
        ring
      rw [hcc, Complex.ofReal_re]
      have hχ2 : ‖sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π)‖ ^ 2 ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (norm_sexticSymbol_prod_le_one (hs i hi) _)
      calc ‖c i‖ ^ 2 * ‖sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π)‖ ^ 2 *
            (f (B (euclideanIntegerPoint n))).re
          ≤ ‖c i‖ ^ 2 * 1 * (f (B (euclideanIntegerPoint n))).re :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hχ2 (sq_nonneg _)) (hf_nonneg _)
        _ = ‖c i‖ ^ 2 * (f (B (euclideanIntegerPoint n))).re := by ring
    have hoff : ∀ j ∈ F.erase i,
        (∑' n : Z, term i j n) ≤
          ‖c i‖ * ‖c j‖ * ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ := by
      intro j hj
      have hjF : j ∈ F := Finset.mem_of_mem_erase hj
      have hre_tsum : (∑' n : Z, term i j n) =
          ((c i * conj (c j)) * sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)).re := by
        dsimp only [term]
        rw [← Complex.reCLM_apply]
        have h := (Complex.reCLM.map_tsum
          ((summable_sexticGramTerm f B (hs i hi) (hs j hjF)).mul_left (c i * conj (c j)))).symm
        rw [tsum_mul_left] at h
        exact h
      rw [hre_tsum]
      calc ((c i * conj (c j)) * sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)).re
          ≤ ‖(c i * conj (c j)) * sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ :=
            Complex.re_le_norm _
        _ = ‖c i‖ * ‖c j‖ * ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ := by
            rw [norm_mul, norm_mul, RCLike.norm_conj]
    exact add_le_add hdiag (Finset.sum_le_sum hoff)
  refine (Finset.sum_le_sum hrow_split).trans ?_
  rw [Finset.sum_add_distrib]
  have hschur :
      (∑ i ∈ F, ∑ j ∈ F.erase i, ‖c i‖ * ‖c j‖ *
          ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) ≤
        ∑ i ∈ F, ‖c i‖ ^ 2 *
          ∑ j ∈ F.erase i, ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ := by
    have hstep1 :
        (∑ i ∈ F, ∑ j ∈ F.erase i, ‖c i‖ * ‖c j‖ *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) ≤
          ∑ i ∈ F, ∑ j ∈ F.erase i, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      have h2 := two_mul_le_add_sq ‖c i‖ ‖c j‖
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hsym_sum :
        (∑ i ∈ F, ∑ j ∈ F.erase i, ‖c j‖ ^ 2 *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) =
          ∑ i ∈ F, ∑ j ∈ F.erase i, ‖c i‖ ^ 2 *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ := by
      have hite_L : (∑ i ∈ F, ∑ j ∈ F.erase i, ‖c j‖ ^ 2 *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) =
          ∑ i ∈ F, ∑ j ∈ F, if j = i then 0 else ‖c j‖ ^ 2 *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.add_sum_erase F _ hi, if_pos rfl, zero_add]
        exact Finset.sum_congr rfl fun j hj => (if_neg (Finset.ne_of_mem_erase hj)).symm
      have hite_R : (∑ j ∈ F, ∑ i ∈ F.erase j, ‖c j‖ ^ 2 *
            ‖sexticGramEntry f B (∏ π ∈ s j, π) (∏ π ∈ s i, π)‖) =
          ∑ j ∈ F, ∑ i ∈ F, if i = j then 0 else ‖c j‖ ^ 2 *
            ‖sexticGramEntry f B (∏ π ∈ s j, π) (∏ π ∈ s i, π)‖ := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.add_sum_erase F _ hj, if_pos rfl, zero_add]
        exact Finset.sum_congr rfl fun i hi => (if_neg (Finset.ne_of_mem_erase hi)).symm
      rw [hite_L, Finset.sum_comm]
      have hcongr : (∑ j ∈ F, ∑ i ∈ F, if j = i then 0 else ‖c j‖ ^ 2 *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) =
          ∑ j ∈ F, ∑ i ∈ F, if i = j then 0 else ‖c j‖ ^ 2 *
            ‖sexticGramEntry f B (∏ π ∈ s j, π) (∏ π ∈ s i, π)‖ := by
        refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg (Ne.symm hij), if_neg hij,
            norm_sexticGramEntry_symm f B hf_real (hs i hi) (hs j hj)]
      rw [hcongr, ← hite_R]
    refine hstep1.trans (le_of_eq ?_)
    have hexp :
        (∑ i ∈ F, ∑ j ∈ F.erase i, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) *
            ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) =
          (1 / 2) * (∑ i ∈ F, ∑ j ∈ F.erase i, ‖c i‖ ^ 2 *
              ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) +
            (1 / 2) * (∑ i ∈ F, ∑ j ∈ F.erase i, ‖c j‖ ^ 2 *
              ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) := by
      simp_rw [add_div, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hexp, hsym_sum, ← add_mul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_mul]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hrhs_eq :
      (∑ i ∈ F, ‖c i‖ ^ 2 * (∑' n : Z, (f (B (euclideanIntegerPoint n))).re)) +
          (∑ i ∈ F, ‖c i‖ ^ 2 *
            ∑ j ∈ F.erase i, ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) =
        ∑ i ∈ F, ‖c i‖ ^ 2 *
          ((∑' n : Z, (f (B (euclideanIntegerPoint n))).re) +
            ∑ j ∈ F.erase i, ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (mul_add _ _ _).symm
  linarith [hschur, hrhs_eq]

/-- **Uniform smooth Schur sextic large sieve over `ℤ[ω]`.** Whenever every off-diagonal row sum of
`‖sexticGramEntry‖` is bounded by `Δ`, the smooth `L²` norm is at most `(∑_n Re f(Bn) + Δ) ∑ ‖c_i‖²`. -/
theorem short_sextic_large_sieve {I : Type*} [DecidableEq I]
    (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E)
    (hf_real : ∀ v : E, f v = ((f v).re : ℂ)) (hf_nonneg : ∀ v : E, 0 ≤ (f v).re)
    (F : Finset I) (s : I → Finset O) (hs : ∀ i ∈ F, IsGoodPrimeSet (s i)) (c : I → ℂ)
    {Δ : ℝ} (hΔ : ∀ i ∈ F,
      ∑ j ∈ F.erase i, ‖sexticGramEntry f B (∏ π ∈ s i, π) (∏ π ∈ s j, π)‖ ≤ Δ) :
    (∑' n : Z, (f (B (euclideanIntegerPoint n))).re *
        ‖∑ i ∈ F, c i * sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s i, π)‖ ^ 2) ≤
      ((∑' n : Z, (f (B (euclideanIntegerPoint n))).re) + Δ) * ∑ i ∈ F, ‖c i‖ ^ 2 := by
  refine (short_sextic_large_sieve_rowwise f B hf_real hf_nonneg F s hs c).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [mul_comm (_ + Δ)]
  exact mul_le_mul_of_nonneg_left (by linarith [hΔ i hi]) (sq_nonneg _)

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
