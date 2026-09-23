import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPieceScales
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayerChains

/-!
# Literal Proposition 2.2 piece types

These definitions encode the three displayed alternatives in Matomäki--Teräväinen Proposition 2.2.
Intervals are exactly half-open on the left and closed on the right.  The Type-II short coefficient
is the literal number of ordered prime tuples from its fixed blocks, as in equation (2.11).
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Source convention: a complex sequence is bounded by one fixed power of the divisor function. -/
def MTPolynomialDivisorBounded (α : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ K : ℕ, ∀ {n : ℕ}, 0 < n →
    ‖α n‖ ≤ C * (n.divisors.card : ℝ) ^ K

/-- Coefficient-level Dirichlet convolution. -/
def mtCoefficientConvolution (α β : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, α d * β (n / d)

/-- Divisor-bounded sequences are closed under Dirichlet convolution. -/
theorem MTPolynomialDivisorBounded.convolution
    {α β : ℕ → ℂ}
    (hα : MTPolynomialDivisorBounded α)
    (hβ : MTPolynomialDivisorBounded β) :
    MTPolynomialDivisorBounded (mtCoefficientConvolution α β) := by
  obtain ⟨C, hC, K, hα⟩ := hα
  obtain ⟨D, hD, L, hβ⟩ := hβ
  refine ⟨C * D, mul_nonneg hC hD, K + L + 1, ?_⟩
  intro n hn
  let T : ℝ := (n.divisors.card : ℝ)
  have hterm : ∀ d ∈ n.divisors,
      ‖α d * β (n / d)‖ ≤ (C * T ^ K) * (D * T ^ L) := by
    intro d hd
    have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
    have hquotPos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdDvd) hdPos
    have hquotDvd : n / d ∣ n := ⟨d, (Nat.div_mul_cancel hdDvd).symm⟩
    have hdCard : (d.divisors.card : ℝ) ≤ T := by
      dsimp [T]
      exact_mod_cast card_divisors_mono_of_dvd hdDvd hn.ne'
    have hquotCard : ((n / d).divisors.card : ℝ) ≤ T := by
      dsimp [T]
      exact_mod_cast card_divisors_mono_of_dvd hquotDvd hn.ne'
    have hα' : ‖α d‖ ≤ C * T ^ K :=
      (hα hdPos).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hdCard K) hC)
    have hβ' : ‖β (n / d)‖ ≤ D * T ^ L :=
      (hβ hquotPos).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hquotCard L) hD)
    rw [norm_mul]
    exact mul_le_mul hα' hβ' (norm_nonneg _) (mul_nonneg hC (by positivity))
  calc
    ‖mtCoefficientConvolution α β n‖ ≤
        ∑ d ∈ n.divisors, ‖α d * β (n / d)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (C * T ^ K) * (D * T ^ L) :=
      Finset.sum_le_sum hterm
    _ = (C * D) * T ^ (K + L + 1) := by
      simp [Finset.sum_const, nsmul_eq_mul, T, pow_add]
      ring

/-- Pointwise restriction preserves divisor-boundedness. -/
theorem MTPolynomialDivisorBounded.restrict
    {α : ℕ → ℂ} (hα : MTPolynomialDivisorBounded α) (P : ℕ → Prop) [DecidablePred P] :
    MTPolynomialDivisorBounded (fun n => if P n then α n else 0) := by
  obtain ⟨C, hC, K, hbound⟩ := hα
  refine ⟨C, hC, K, ?_⟩
  intro n hn
  by_cases hP : P n
  · simpa [hP] using hbound hn
  · simp [hP, mul_nonneg hC (by positivity : 0 ≤ (n.divisors.card : ℝ) ^ K)]

/-- Coefficient sequence restricted to the exact real interval `(M,N]`. -/
def mtRealIntervalAF (α : ℕ → ℂ) (M N : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else if M < (n : ℝ) ∧ (n : ℝ) ≤ N then α n else 0,
    by simp⟩

@[simp] theorem mtRealIntervalAF_apply_of_pos
    (α : ℕ → ℂ) (M N : ℝ) {n : ℕ} (hn : 0 < n) :
    mtRealIntervalAF α M N n = if M < (n : ℝ) ∧ (n : ℝ) ≤ N then α n else 0 := by
  simp [mtRealIntervalAF, hn.ne']

/-- Type-I function in Proposition 2.2(i). -/
def mtTypeIPieceAF (α : ℕ → ℂ) (M₁ M₂ δ : ℝ) : ArithmeticFunction ℂ :=
  mtRealIntervalAF α M₁ (2 * M₁) *
    mtRealIntervalAF (fun _ => 1) M₂ ((1 + δ) * M₂)

/-- Pointwise form of the exact two-variable Type-I sum. -/
theorem mtTypeIPieceAF_apply (α : ℕ → ℂ) (M₁ M₂ δ : ℝ)
    {n : ℕ} (hn : 0 < n) :
    mtTypeIPieceAF α M₁ M₂ δ n =
      ∑ m₁ ∈ n.divisors,
        if M₁ < (m₁ : ℝ) ∧ (m₁ : ℝ) ≤ 2 * M₁ ∧
            M₂ < ((n / m₁ : ℕ) : ℝ) ∧
              ((n / m₁ : ℕ) : ℝ) ≤ (1 + δ) * M₂
        then α m₁ else 0 := by
  rw [mtTypeIPieceAF, ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ n.divisorsAntidiagonal,
      mtRealIntervalAF α M₁ (2 * M₁) x.1 *
        mtRealIntervalAF (fun _ => 1) M₂ ((1 + δ) * M₂) x.2) =
      ∑ m₁ ∈ n.divisors,
          mtRealIntervalAF α M₁ (2 * M₁) m₁ *
          mtRealIntervalAF (fun _ => 1) M₂ ((1 + δ) * M₂) (n / m₁) by
    exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
      (fun m q => mtRealIntervalAF α M₁ (2 * M₁) m *
        mtRealIntervalAF (fun _ => 1) M₂ ((1 + δ) * M₂) q)]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  have hm₁Pos : 0 < m₁ := Nat.pos_of_mem_divisors hm₁
  have hquotPos : 0 < n / m₁ :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hm₁)) hm₁Pos
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hm₁Pos,
    mtRealIntervalAF_apply_of_pos _ _ _ hquotPos]
  by_cases h₁ : M₁ < (m₁ : ℝ) ∧ (m₁ : ℝ) ≤ 2 * M₁
  · by_cases h₂ : M₂ < ((n / m₁ : ℕ) : ℝ) ∧
        ((n / m₁ : ℕ) : ℝ) ≤ (1 + δ) * M₂
    · simp [h₁.1, h₁.2, h₂.1, h₂.2]
    · simp [h₁, h₂]
  · have hcond : ¬(M₁ < (m₁ : ℝ) ∧ (m₁ : ℝ) ≤ 2 * M₁ ∧
        M₂ < ((n / m₁ : ℕ) : ℝ) ∧
          ((n / m₁ : ℕ) : ℝ) ≤ (1 + δ) * M₂) := by tauto
    simp [h₁, hcond]

/-- Type-I/II function in Proposition 2.2(ii). -/
def mtTypeI_II_PieceAF
    (α β : ℕ → ℂ) (M₁ M₂ M₃ δ : ℝ) : ArithmeticFunction ℂ :=
  (mtRealIntervalAF α M₁ (2 * M₁) * mtRealIntervalAF β M₂ (2 * M₂)) *
    mtRealIntervalAF (fun _ => 1) M₃ ((1 + δ) * M₃)

/-- Ordered choices of one prime from every index in a selected Type-II block family. -/
def mtTypeIIPrimeTuples (I : Finset ℕ) (block : ℕ → Finset ℕ) (m : ℕ) :
    Finset (I → ℕ) :=
  (Fintype.piFinset fun i : I => block i).filter fun q => ∏ i, q i = m

/-- Literal equation-(2.11) coefficient: sum of `1` over ordered block-prime factorizations. -/
def mtTypeIIPrimeCoefficient (I : Finset ℕ) (block : ℕ → Finset ℕ) (m : ℕ) : ℂ :=
  (mtTypeIIPrimeTuples I block m).card

theorem mtTypeIIPrimeCoefficient_eq_source_sum
    (I : Finset ℕ) (block : ℕ → Finset ℕ) (m : ℕ) :
    mtTypeIIPrimeCoefficient I block m =
      ∑ q ∈ Fintype.piFinset (fun i : I => block i),
        if (∏ i, q i) = m then 1 else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp [mtTypeIIPrimeCoefficient, mtTypeIIPrimeTuples, Finset.sum_const, nsmul_eq_mul]

theorem mem_mtTypeIIPrimeTuples {I : Finset ℕ} {block : ℕ → Finset ℕ}
    {m : ℕ} {q : I → ℕ} :
    q ∈ mtTypeIIPrimeTuples I block m ↔
      (∀ i : I, q i ∈ block i) ∧ ∏ i, q i = m := by
  simp [mtTypeIIPrimeTuples, Fintype.mem_piFinset]

/-- Equation-(2.11) coefficients are divisor-bounded with the literal exponent `R`. -/
theorem card_mtTypeIIPrimeTuples_le_divisors_pow
    {I : Finset ℕ} {block : ℕ → Finset ℕ}
    {m : ℕ} (hm : 0 < m) :
    (mtTypeIIPrimeTuples I block m).card ≤ m.divisors.card ^ I.card := by
  classical
  have hmaps : ∀ q ∈ mtTypeIIPrimeTuples I block m,
      q ∈ Fintype.piFinset (fun _ : I => m.divisors) := by
    intro q hq
    rw [Fintype.mem_piFinset]
    intro i
    rw [Nat.mem_divisors]
    refine ⟨?_, hm.ne'⟩
    have hprod : ∏ j, q j = m := (mem_mtTypeIIPrimeTuples.mp hq).2
    rw [← hprod]
    exact Finset.dvd_prod_of_mem q (Finset.mem_univ i)
  have hcard := Finset.card_le_card_of_injOn
    (f := fun q : I → ℕ => q) hmaps
    (fun q hq r hr hqr => hqr)
  calc
    (mtTypeIIPrimeTuples I block m).card ≤
        (Fintype.piFinset (fun _ : I => m.divisors)).card := hcard
    _ = m.divisors.card ^ I.card := by
      rw [Fintype.card_piFinset]
      simp [Finset.prod_const]

theorem mtTypeIIPrimeCoefficient_polynomialDivisorBounded
    {I : Finset ℕ} {block : ℕ → Finset ℕ} :
    MTPolynomialDivisorBounded (mtTypeIIPrimeCoefficient I block) := by
  refine ⟨1, by norm_num, I.card, ?_⟩
  intro m hm
  have hcard := card_mtTypeIIPrimeTuples_le_divisors_pow (I := I) (block := block) hm
  simpa [mtTypeIIPrimeCoefficient] using (show
    ((mtTypeIIPrimeTuples I block m).card : ℝ) ≤
      (m.divisors.card : ℝ) ^ I.card by exact_mod_cast hcard)

/-- Type-II function in Proposition 2.2(iii), with its exact equation-(2.11) coefficient. -/
def mtTypeIIPieceAF (I : Finset ℕ) (block : ℕ → Finset ℕ)
    (β : ℕ → ℂ) (M₁ M₂ δ : ℝ) : ArithmeticFunction ℂ :=
  mtRealIntervalAF (mtTypeIIPrimeCoefficient I block)
      M₁ ((1 + δ) ^ I.card * M₁) *
    mtRealIntervalAF β M₂ (2 * M₂)

/-- Pointwise form of the exact two-variable Type-II sum. -/
theorem mtTypeIIPieceAF_apply
    (I : Finset ℕ) (block : ℕ → Finset ℕ)
    (β : ℕ → ℂ) (M₁ M₂ δ : ℝ) {n : ℕ} (hn : 0 < n) :
    mtTypeIIPieceAF I block β M₁ M₂ δ n =
      ∑ m₁ ∈ n.divisors,
        if M₁ < (m₁ : ℝ) ∧
            (m₁ : ℝ) ≤ (1 + δ) ^ I.card * M₁ ∧
            M₂ < ((n / m₁ : ℕ) : ℝ) ∧ ((n / m₁ : ℕ) : ℝ) ≤ 2 * M₂
        then mtTypeIIPrimeCoefficient I block m₁ * β (n / m₁) else 0 := by
  rw [mtTypeIIPieceAF, ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ n.divisorsAntidiagonal,
      mtRealIntervalAF (mtTypeIIPrimeCoefficient I block)
          M₁ ((1 + δ) ^ I.card * M₁) x.1 *
        mtRealIntervalAF β M₂ (2 * M₂) x.2) =
      ∑ m₁ ∈ n.divisors,
        mtRealIntervalAF (mtTypeIIPrimeCoefficient I block)
            M₁ ((1 + δ) ^ I.card * M₁) m₁ *
          mtRealIntervalAF β M₂ (2 * M₂) (n / m₁) by
    exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
      (fun m q => mtRealIntervalAF (mtTypeIIPrimeCoefficient I block)
          M₁ ((1 + δ) ^ I.card * M₁) m * mtRealIntervalAF β M₂ (2 * M₂) q)]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  have hm₁Pos : 0 < m₁ := Nat.pos_of_mem_divisors hm₁
  have hquotPos : 0 < n / m₁ :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hm₁)) hm₁Pos
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hm₁Pos,
    mtRealIntervalAF_apply_of_pos _ _ _ hquotPos]
  by_cases h₁ : M₁ < (m₁ : ℝ) ∧
      (m₁ : ℝ) ≤ (1 + δ) ^ I.card * M₁
  · by_cases h₂ : M₂ < ((n / m₁ : ℕ) : ℝ) ∧ ((n / m₁ : ℕ) : ℝ) ≤ 2 * M₂
    · simp [h₁.1, h₁.2, h₂.1, h₂.2]
    · simp [h₁, h₂]
  · have hcond : ¬(M₁ < (m₁ : ℝ) ∧
        (m₁ : ℝ) ≤ (1 + δ) ^ I.card * M₁ ∧
        M₂ < ((n / m₁ : ℕ) : ℝ) ∧ ((n / m₁ : ℕ) : ℝ) ≤ 2 * M₂) := by tauto
    simp [h₁, hcond]

/-- Complete witness for Proposition 2.2(i). -/
structure MTTypeIPieceData (X Y δ ε : ℝ) where
  M₁ : ℝ
  M₂ : ℝ
  α : ℕ → ℂ
  M₁_pos : 0 < M₁
  M₂_pos : 0 < M₂
  α_divisorBounded : MTPolynomialDivisorBounded α
  M₁_le : M₁ ≤ X ^ (1 / 2 + ε)
  product_mem : Y / 2 < M₁ * M₂ ∧ M₁ * M₂ ≤ 4 * Y

def MTTypeIPieceData.pieceAF {X Y δ ε : ℝ}
    (data : MTTypeIPieceData X Y δ ε) : ArithmeticFunction ℂ :=
  mtTypeIPieceAF data.α data.M₁ data.M₂ δ

/-- Complete witness for Proposition 2.2(ii). -/
structure MTTypeI_II_PieceData (X Y δ ε : ℝ) where
  M₁ : ℝ
  M₂ : ℝ
  M₃ : ℝ
  α : ℕ → ℂ
  β : ℕ → ℂ
  M₁_pos : 0 < M₁
  M₂_pos : 0 < M₂
  M₃_pos : 0 < M₃
  α_divisorBounded : MTPolynomialDivisorBounded α
  β_divisorBounded : MTPolynomialDivisorBounded β
  square_product_le : M₁ ^ (2 : ℕ) * M₂ ≤ X ^ (1 - ε)
  M₂_le : M₂ ≤ X ^ (1 / 4 - ε)
  product_mem : Y / 2 < M₁ * M₂ * M₃ ∧ M₁ * M₂ * M₃ ≤ 4 * Y

def MTTypeI_II_PieceData.pieceAF {X Y δ ε : ℝ}
    (data : MTTypeI_II_PieceData X Y δ ε) : ArithmeticFunction ℂ :=
  mtTypeI_II_PieceAF data.α data.β data.M₁ data.M₂ data.M₃ δ

/-- Complete witness for Proposition 2.2(iii), including every condition around equation (2.11). -/
structure MTTypeIIPieceData (X Y z₀ z δ ε : ℝ) where
  indices : Finset ℕ
  R_pos : 1 ≤ indices.card
  R_le : indices.card ≤ Nat.floor (Real.log z / Real.log z₀)
  Q : ℕ → ℝ
  block : ℕ → Finset ℕ
  M₁ : ℝ
  M₂ : ℝ
  β : ℕ → ℂ
  z₀_pos : 0 < z₀
  δ_nonneg : 0 ≤ δ
  Q_mem : ∀ i ∈ indices, z₀ ≤ Q i ∧ Q i < z
  block_eq : ∀ i ∈ indices, ∀ q, q ∈ block i ↔
    q.Prime ∧ Q i < (q : ℝ) ∧ (q : ℝ) ≤ Q i * (1 + δ)
  M₁_eq : M₁ = ∏ i : indices, Q i
  M₁_mem : X ^ (ε / 2) ≤ M₁ ∧ M₁ ≤ z
  M₂_pos : 0 < M₂
  β_divisorBounded : MTPolynomialDivisorBounded β
  product_mem : Y / 2 < M₁ * M₂ ∧ M₁ * M₂ ≤ 4 * Y

def MTTypeIIPieceData.pieceAF {X Y z₀ z δ ε : ℝ}
    (data : MTTypeIIPieceData X Y z₀ z δ ε) : ArithmeticFunction ℂ :=
  mtTypeIIPieceAF data.indices data.block data.β data.M₁ data.M₂ δ

/-- Equation-(2.11) coefficient is supported on the exact source interval
`(M₁,(1+δ)^R M₁]`. -/
theorem MTTypeIIPieceData.primeCoefficient_support
    {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    {m : ℕ} (hm : mtTypeIIPrimeCoefficient data.indices data.block m ≠ 0) :
    data.M₁ < (m : ℝ) ∧
      (m : ℝ) ≤ (1 + δ) ^ data.indices.card * data.M₁ := by
  classical
  have hcard : (mtTypeIIPrimeTuples data.indices data.block m).card ≠ 0 := by
    intro hzero
    apply hm
    simp [mtTypeIIPrimeCoefficient, hzero]
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
  have htuple := mem_mtTypeIIPrimeTuples.mp hq
  have hprodCast : ∏ i, (q i : ℝ) = (m : ℝ) := by
    exact_mod_cast htuple.2
  have hQpos : ∀ i ∈ (Finset.univ : Finset data.indices), 0 < data.Q i := by
    intro i hi
    exact data.z₀_pos.trans_le (data.Q_mem i i.property).1
  have hQq : ∀ i ∈ (Finset.univ : Finset data.indices),
      data.Q i ≤ (q i : ℝ) := by
    intro i hi
    exact (data.block_eq i i.property (q i)).mp (htuple.1 i) |>.2.1.le
  obtain ⟨i₀, hi₀⟩ := data.indices.card_pos.mp data.R_pos
  let i₀' : data.indices := ⟨i₀, hi₀⟩
  have hlower : (∏ i : data.indices, data.Q i) < ∏ i, (q i : ℝ) := by
    apply Finset.prod_lt_prod hQpos hQq
    exact ⟨i₀', Finset.mem_univ _,
      (data.block_eq i₀ hi₀ (q i₀')).mp (htuple.1 i₀') |>.2.1⟩
  have hqupper : ∀ i ∈ (Finset.univ : Finset data.indices),
      (q i : ℝ) ≤ data.Q i * (1 + δ) := by
    intro i hi
    exact (data.block_eq i i.property (q i)).mp (htuple.1 i) |>.2.2
  have hupper : ∏ i, (q i : ℝ) ≤
      ∏ i : data.indices, (data.Q i * (1 + δ)) := by
    exact Finset.prod_le_prod
      (fun i hi => Nat.cast_nonneg (q i)) hqupper
  constructor
  · rw [data.M₁_eq, ← hprodCast]
    exact hlower
  · rw [← hprodCast, data.M₁_eq]
    calc
      ∏ i, (q i : ℝ) ≤ ∏ i : data.indices, (data.Q i * (1 + δ)) := hupper
      _ = (1 + δ) ^ data.indices.card * ∏ i : data.indices, data.Q i := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.prod_const]
        ring

/-- A function has one of the three exact forms asserted by Proposition 2.2. -/
inductive MTProposition22Piece (X Y z₀ z δ ε : ℝ) : ArithmeticFunction ℂ → Prop
  | typeI (data : MTTypeIPieceData X Y δ ε) :
      MTProposition22Piece X Y z₀ z δ ε data.pieceAF
  | typeI_II (data : MTTypeI_II_PieceData X Y δ ε) :
      MTProposition22Piece X Y z₀ z δ ε data.pieceAF
  | typeII (data : MTTypeIIPieceData X Y z₀ z δ ε) :
      MTProposition22Piece X Y z₀ z δ ε data.pieceAF

end

end RHTower.Sieve
