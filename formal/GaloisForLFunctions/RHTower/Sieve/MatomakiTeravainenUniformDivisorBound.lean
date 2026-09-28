import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPairBoxClassification
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSeparatedBoxBoundaryMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanSourceCoefficients

/-!
# Uniform divisor bounds for the Proposition 2.2 pieces

`MTUniformDivisorBounded K α` is `|α(n)| ≤ d(n)^K` with a *fixed* exponent.  Dirichlet
convolution adds the exponents plus one.  The recursive prime blocks of a minimal geometric
schedule are pairwise disjoint sets of primes, so a product of distinct blocks has coefficients
in `{0, 1}`: this is what keeps the exponent of a Buchstab chain independent of its length.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Divisor bound with a fixed exponent and constant one. -/
def MTUniformDivisorBounded (K : ℕ) (α : ℕ → ℂ) : Prop :=
  ∀ ⦃n : ℕ⦄, 0 < n → ‖α n‖ ≤ (n.divisors.card : ℝ) ^ K

theorem one_le_card_divisors_real {n : ℕ} (hn : 0 < n) : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
  have : 1 ≤ n.divisors.card := Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hn.ne'⟩
  exact_mod_cast this

theorem MTUniformDivisorBounded.mono {K L : ℕ} {α : ℕ → ℂ} (hKL : K ≤ L)
    (h : MTUniformDivisorBounded K α) : MTUniformDivisorBounded L α := fun n hn =>
  (h hn).trans (pow_le_pow_right₀ (one_le_card_divisors_real hn) hKL)

theorem MTUniformDivisorBounded.polynomial {K : ℕ} {α : ℕ → ℂ}
    (h : MTUniformDivisorBounded K α) : MTPolynomialDivisorBounded α :=
  ⟨1, zero_le_one, K, fun hn => by simpa using h hn⟩

theorem MTUniformDivisorBounded.of_norm_le_one {α : ℕ → ℂ} (h : ∀ n, ‖α n‖ ≤ 1) :
    MTUniformDivisorBounded 0 α := fun n _ => by simpa using h n

theorem MTUniformDivisorBounded.convolution {K L : ℕ} {α β : ℕ → ℂ}
    (hα : MTUniformDivisorBounded K α) (hβ : MTUniformDivisorBounded L β) :
    MTUniformDivisorBounded (K + L + 1) (mtCoefficientConvolution α β) := by
  intro n hn
  have hterm : ∀ d ∈ n.divisors, ‖α d * β (n / d)‖ ≤
      (n.divisors.card : ℝ) ^ K * (n.divisors.card : ℝ) ^ L := by
    intro d hd
    have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
    have hquotPos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdDvd) hdPos
    have hquotDvd : n / d ∣ n := ⟨d, (Nat.div_mul_cancel hdDvd).symm⟩
    have hdCard : (d.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_mono_of_dvd hdDvd hn.ne'
    have hquotCard : ((n / d).divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_mono_of_dvd hquotDvd hn.ne'
    rw [norm_mul]
    exact mul_le_mul ((hα hdPos).trans (pow_le_pow_left₀ (by positivity) hdCard K))
      ((hβ hquotPos).trans (pow_le_pow_left₀ (by positivity) hquotCard L))
      (norm_nonneg _) (by positivity)
  calc ‖mtCoefficientConvolution α β n‖ ≤ ∑ d ∈ n.divisors, ‖α d * β (n / d)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (n.divisors.card : ℝ) ^ K * (n.divisors.card : ℝ) ^ L :=
        Finset.sum_le_sum hterm
    _ = (n.divisors.card : ℝ) ^ (K + L + 1) := by
        simp [Finset.sum_const, nsmul_eq_mul, pow_add]
        ring

theorem MTUniformDivisorBounded.arithmeticFunction_mul {K L : ℕ} {F G : ArithmeticFunction ℂ}
    (hF : MTUniformDivisorBounded K (fun n => F n)) (hG : MTUniformDivisorBounded L (fun n => G n)) :
    MTUniformDivisorBounded (K + L + 1) (fun n => (F * G) n) := by
  rw [← mtCoefficientConvolution_eq_arithmeticFunction_mul]
  exact hF.convolution hG

theorem MTUniformDivisorBounded.arithmeticFunction_smul {K : ℕ} {F : ArithmeticFunction ℂ}
    (hF : MTUniformDivisorBounded K (fun n => F n)) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    MTUniformDivisorBounded K (fun n => (c • F) n) := by
  intro n hn
  change ‖c * F n‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hF hn)

theorem MTUniformDivisorBounded.realInterval {K : ℕ} {α : ℕ → ℂ}
    (h : MTUniformDivisorBounded K α) (M N : ℝ) :
    MTUniformDivisorBounded K (fun n => mtRealIntervalAF α M N n) := by
  intro n hn
  change ‖mtRealIntervalAF α M N n‖ ≤ _
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hn]
  split
  · exact h hn
  · simp

theorem MTUniformDivisorBounded.coefficientAF {K : ℕ} {α : ℕ → ℂ}
    (h : MTUniformDivisorBounded K α) :
    MTUniformDivisorBounded K (fun n => mtCoefficientAF α n) := by
  intro n hn
  change ‖mtCoefficientAF α n‖ ≤ _
  rw [mtCoefficientAF_apply_of_pos _ hn]
  exact h hn

theorem mtUnitCoefficient_uniformDivisorBounded :
    MTUniformDivisorBounded 0 mtUnitCoefficient :=
  MTUniformDivisorBounded.of_norm_le_one norm_mtUnitCoefficient_le_one

theorem mtFinsetIndicatorCoefficient_uniformDivisorBounded (S : Finset ℕ) :
    MTUniformDivisorBounded 0 (mtFinsetIndicatorCoefficient S) :=
  MTUniformDivisorBounded.of_norm_le_one (norm_mtFinsetIndicatorCoefficient_le_one S)

theorem mtTruncLegendreCoefficient_uniformDivisorBounded (z D : ℕ) :
    MTUniformDivisorBounded 0 (mtTruncLegendreCoefficient z D) := by
  refine MTUniformDivisorBounded.of_norm_le_one fun n => ?_
  unfold mtTruncLegendreCoefficient
  split
  · rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp

theorem mtUpperAdicOneAF_uniformDivisorBounded (δ : ℝ) (j : ℕ) :
    MTUniformDivisorBounded 0 (fun n => mtUpperAdicOneAF δ j n) :=
  (MTUniformDivisorBounded.of_norm_le_one (α := fun _ => (1 : ℂ)) (by simp)).realInterval _ _

theorem mtHarmanPairCellCoefficient_uniformDivisorBounded (S₁ S₂ : Finset ℕ) :
    MTUniformDivisorBounded 2 (mtHarmanPairCellCoefficient S₁ S₂) := by
  intro m hm
  have hcard := card_mtHarmanPairCellTuples_le_divisors_sq (S₁ := S₁) (S₂ := S₂) hm
  simpa [mtHarmanPairCellCoefficient] using (show
    ((mtHarmanPairCellTuples S₁ S₂ m).card : ℝ) ≤ (m.divisors.card : ℝ) ^ (2 : ℕ) by
      exact_mod_cast hcard)

theorem mtHarmanTripleCellCoefficient_uniformDivisorBounded (S₁ S₂ S₃ : Finset ℕ) :
    MTUniformDivisorBounded 2 (mtHarmanTripleCellCoefficient S₁ S₂ S₃) := by
  intro m hm
  have hcard := card_mtHarmanTripleCellTuples_le_divisors_sq (S₁ := S₁) (S₂ := S₂) (S₃ := S₃) hm
  simpa [mtHarmanTripleCellCoefficient] using (show
    ((mtHarmanTripleCellTuples S₁ S₂ S₃ m).card : ℝ) ≤ (m.divisors.card : ℝ) ^ (2 : ℕ) by
      exact_mod_cast hcard)

/-- Pairwise disjoint prime blocks give at most one ordered factorization. -/
theorem card_mtTypeIIPrimeTuples_le_one {I : Finset ℕ} {block : ℕ → Finset ℕ}
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (block i) (block j))
    (hprime : ∀ i ∈ I, ∀ q ∈ block i, q.Prime) (m : ℕ) :
    (mtTypeIIPrimeTuples I block m).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 fun q hq r hr => ?_
  obtain ⟨hqmem, hqprod⟩ := mem_mtTypeIIPrimeTuples.1 hq
  obtain ⟨hrmem, hrprod⟩ := mem_mtTypeIIPrimeTuples.1 hr
  funext i
  have hqi : (q i).Prime := hprime i i.2 _ (hqmem i)
  have hdvd : q i ∣ ∏ j, r j := by
    rw [hrprod, ← hqprod]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨j, -, hj⟩ := (Nat.Prime.prime hqi).exists_mem_finset_dvd hdvd
  have hrj : (r j).Prime := hprime j j.2 _ (hrmem j)
  have heq : q i = r j := (Nat.prime_dvd_prime_iff_eq hqi hrj).1 hj
  by_cases hij : (i : ℕ) = j
  · have : i = j := Subtype.ext hij
    subst this; exact heq
  · exfalso
    exact Finset.disjoint_left.1 (hdisj i i.2 j j.2 hij) (hqmem i) (heq ▸ hrmem j)

theorem mtTypeIIPrimeCoefficient_uniformDivisorBounded {I : Finset ℕ} {block : ℕ → Finset ℕ}
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (block i) (block j))
    (hprime : ∀ i ∈ I, ∀ q ∈ block i, q.Prime) :
    MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient I block) := by
  refine MTUniformDivisorBounded.of_norm_le_one fun m => ?_
  rw [mtTypeIIPrimeCoefficient, Complex.norm_natCast]
  exact_mod_cast card_mtTypeIIPrimeTuples_le_one hdisj hprime m

/-- A product of pairwise disjoint prime blocks has coefficients in `{0, 1}`. -/
theorem mtPrimeBlockFamilyAF_uniformDivisorBounded {t : ℕ} (block : Fin t → Finset ℕ)
    (S : Finset (Fin t))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (block i) (block j))
    (hprime : ∀ i ∈ S, ∀ q ∈ block i, q.Prime) :
    MTUniformDivisorBounded 0 (fun n => mtPrimeBlockFamilyAF block S n) := by
  rw [mtPrimeBlockFamilyAF_eq_enumeratedTypeIIPrimeCoefficientAF block S
    (fun i hi m hm => (hprime i hi m hm).pos)]
  refine MTUniformDivisorBounded.coefficientAF
    (mtTypeIIPrimeCoefficient_uniformDivisorBounded ?_ ?_)
  · intro i hi j hj hij
    have hi' : i < S.card := Finset.mem_range.1 hi
    have hj' : j < S.card := Finset.mem_range.1 hj
    simp only [mtFinBlockToNat, dif_pos hi', dif_pos hj', mtEnumeratedBlock]
    refine hdisj _ (mtFinsetEnumeration_mem S _) _ (mtFinsetEnumeration_mem S _) ?_
    intro h
    exact hij (by simpa using congrArg Fin.val (mtFinsetEnumeration_injective S h))
  · intro i hi q hq
    have hi' : i < S.card := Finset.mem_range.1 hi
    simp only [mtFinBlockToNat, dif_pos hi', mtEnumeratedBlock] at hq
    exact hprime _ (mtFinsetEnumeration_mem S _) q hq

/-- The recursive blocks of a minimal geometric schedule are pairwise disjoint sets of primes. -/
theorem ofMinimalGeometricSchedule_block_disjoint_prime
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z) :
    (∀ i j : Fin (mtMinimalGeometricDepth delta start z hdelta), i ≠ j →
      Disjoint ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block j)) ∧
    (∀ i, ∀ q ∈ (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i, q.Prime) := by
  refine ⟨fun i j hij => ?_, fun i q hq =>
    ((mem_ofMinimalGeometricSchedule_block_iff z0 D start hdelta hz0 hroot i q).1 hq).1⟩
  rw [Finset.disjoint_left]
  intro q hqi hqj
  have hi := (mem_ofMinimalGeometricSchedule_block_iff z0 D start hdelta hz0 hroot i q).1 hqi
  have hj := (mem_ofMinimalGeometricSchedule_block_iff z0 D start hdelta hz0 hroot j q).1 hqj
  have hsucc : ∀ k : ℕ, mtGeometricLevel delta start k * (1 + delta) =
      mtGeometricLevel delta start (k + 1) := by
    intro k; simp only [mtGeometricLevel]; rw [← pow_succ]; ring_nf
  have hmono := mtGeometricLevel_strictMono hdelta start
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · have h1 : mtGeometricLevel delta start (i.1 + 1) ≤ mtGeometricLevel delta start j.1 :=
      hmono.monotone (by omega)
    rw [← hsucc] at h1
    linarith [hi.2.2, hj.2.1]
  · have h1 : mtGeometricLevel delta start (j.1 + 1) ≤ mtGeometricLevel delta start i.1 :=
      hmono.monotone (by omega)
    rw [← hsucc] at h1
    linarith [hj.2.2, hi.2.1]

/-- The Buchstab chain coefficient of a uniformly bounded outer coefficient against disjoint prime
blocks costs one unit of exponent. -/
theorem mtBlockChainCoefficientAF_uniformDivisorBounded {t K : ℕ} {α : ℕ → ℂ}
    {block : Fin t → Finset ℕ} (hα : MTUniformDivisorBounded K α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hprime : ∀ i, ∀ q ∈ block i, q.Prime) (chain : List (Fin t)) :
    MTUniformDivisorBounded (K + 1) (fun n => mtBlockChainCoefficientAF α block chain n) := by
  have h := hα.coefficientAF.arithmeticFunction_mul
    (mtPrimeBlockFamilyAF_uniformDivisorBounded block chain.toFinset
      (fun i _ j _ hij => hdisj i j hij) (fun i _ => hprime i))
  simpa [mtBlockChainCoefficientAF] using h

theorem mtBlockChainLongAF_uniformDivisorBounded {t K : ℕ} {α : ℕ → ℂ}
    {block : Fin t → Finset ℕ} (hα : MTUniformDivisorBounded K α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hprime : ∀ i, ∀ q ∈ block i, q.Prime) (chain : List (Fin t))
    (z D : ℕ) (δ : ℝ) (i : ℕ) :
    MTUniformDivisorBounded (K + 2) (fun n => mtBlockChainLongAF α block chain z D δ i n) := by
  have h := (mtBlockChainCoefficientAF_uniformDivisorBounded hα hdisj hprime chain).arithmeticFunction_mul
    ((mtTruncLegendreCoefficient_uniformDivisorBounded z D).realInterval
      (mtUpperAdicScale δ i) ((1 + δ) * mtUpperAdicScale δ i))
  simpa [mtBlockChainLongAF, mtUpperAdicCoefficientAF] using h

/-- The (2.11) coefficient of a selected minimal geometric Type-II datum is `0` or `1`. -/
theorem mtMinimalGeometricTypeIIData_primeCoefficient_uniformDivisorBounded
    {X Y z0 z delta epsilon M2 : ℝ}
    (z0Nat D start : ℕ) (hdelta : 0 < delta)
    (hz0Nat : (z0Nat : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (S : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hS : S.Nonempty)
    (hz0pos : 0 < z0)
    (hz0level : z0 ≤ mtGeometricLevel delta start 0)
    (hR : S.card ≤ Nat.floor (Real.log z / Real.log z0))
    (beta : ℕ → ℂ) (hM2 : 0 < M2)
    (hbeta : MTPolynomialDivisorBounded beta)
    (hM1 : X ^ (epsilon / 2) ≤ ∏ i ∈ S, mtGeometricLevel delta start i.1 ∧
      (∏ i ∈ S, mtGeometricLevel delta start i.1) ≤ z)
    (hproduct : Y / 2 < (∏ i ∈ S, mtGeometricLevel delta start i.1) * M2 ∧
      (∏ i ∈ S, mtGeometricLevel delta start i.1) * M2 ≤ 4 * Y) :
    MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient
      (mtMinimalGeometricTypeIIData (X := X) (Y := Y) (epsilon := epsilon) z0Nat D start hdelta
        hz0Nat hroot S hS hz0pos hz0level hR beta hM2 hbeta hM1 hproduct).indices
      (mtMinimalGeometricTypeIIData (X := X) (Y := Y) (epsilon := epsilon) z0Nat D start hdelta
        hz0Nat hroot S hS hz0pos hz0level hR beta hM2 hbeta hM1 hproduct).block) := by
  obtain ⟨hdisj, hprime⟩ := ofMinimalGeometricSchedule_block_disjoint_prime z0Nat D start
    hdelta hz0Nat hroot
  have h := mtPrimeBlockFamilyAF_uniformDivisorBounded
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0Nat D start delta z hdelta hz0Nat hroot).block S
    (fun i _ j _ hij => hdisj i j hij) (fun i _ => hprime i)
  rw [mtPrimeBlockFamilyAF_eq_enumeratedTypeIIPrimeCoefficientAF _ S
    (fun i _ m hm => (hprime i m hm).pos)] at h
  intro n hn
  have := h hn
  simp only [mtCoefficientAF_apply_of_pos _ hn] at this
  exact this

/-- Proposition 2.2 pieces with a fixed uniform divisor exponent `K`; the (2.11) coefficient of a
Type-II piece is `0` or `1`. -/
inductive MTUniformProposition22Piece (K : ℕ) (X Y z₀ z δ ε : ℝ) :
    ArithmeticFunction ℂ → Prop
  | typeI (data : MTTypeIPieceData X Y δ ε) (hα : MTUniformDivisorBounded K data.α) :
      MTUniformProposition22Piece K X Y z₀ z δ ε data.pieceAF
  | typeI_II (data : MTTypeI_II_PieceData X Y δ ε) (hα : MTUniformDivisorBounded K data.α)
      (hβ : MTUniformDivisorBounded K data.β) :
      MTUniformProposition22Piece K X Y z₀ z δ ε data.pieceAF
  | typeII (data : MTTypeIIPieceData X Y z₀ z δ ε)
      (hprime : MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block))
      (hβ : MTUniformDivisorBounded K data.β) :
      MTUniformProposition22Piece K X Y z₀ z δ ε data.pieceAF

theorem MTUniformProposition22Piece.toPiece {K : ℕ} {X Y z₀ z δ ε : ℝ}
    {f : ArithmeticFunction ℂ} (hf : MTUniformProposition22Piece K X Y z₀ z δ ε f) :
    MTProposition22Piece X Y z₀ z δ ε f := by
  cases hf with
  | typeI data _ => exact MTProposition22Piece.typeI data
  | typeI_II data _ _ => exact MTProposition22Piece.typeI_II data
  | typeII data _ _ => exact MTProposition22Piece.typeII data

theorem MTUniformProposition22Piece.mono {K L : ℕ} (hKL : K ≤ L) {X Y z₀ z δ ε : ℝ}
    {f : ArithmeticFunction ℂ} (hf : MTUniformProposition22Piece K X Y z₀ z δ ε f) :
    MTUniformProposition22Piece L X Y z₀ z δ ε f := by
  cases hf with
  | typeI data hα => exact MTUniformProposition22Piece.typeI data (hα.mono hKL)
  | typeI_II data hα hβ =>
      exact MTUniformProposition22Piece.typeI_II data (hα.mono hKL) (hβ.mono hKL)
  | typeII data hprime hβ => exact MTUniformProposition22Piece.typeII data hprime (hβ.mono hKL)

end

end RHTower.Sieve
