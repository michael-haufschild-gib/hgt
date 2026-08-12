import GaloisForLFunctions.RHTower.Sieve.MontgomeryVaughanCoefficientSmoothing
import GaloisForLFunctions.RHTower.Sieve.VinogradovLogTaylorRemainder

/-!
# Montgomery--Vaughan convolution receiver

Finite, constant-explicit form of Lemma 24.10 and its specialization to Route T's logarithmic
bilinear phase.  This file contains the additive-convolution rearrangement; coefficient smoothing
is supplied by `MontgomeryVaughanCoefficientSmoothing`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

def mvCoefficientBlockSum (K M : ℕ) (c : Fin K → ℂ) : ℂ :=
  ∑ k : Fin K, c k * if M < k.val ∧ k.val ≤ 2 * M then 1 else 0

def mvPhaseBlockSum (K N N' : ℕ) (d : ℕ → ℂ) : ℂ :=
  ∑ n : Fin K, d n.val * if N < n.val ∧ n.val ≤ N' then 1 else 0

def mvConvolutionSlice
    (K M N N' r : ℕ) (c : Fin K → ℂ) (d : ℕ → ℂ) : ℂ :=
  ∑ k : Fin K,
    c k * d (r - k.val) *
      if M < k.val ∧ k.val ≤ 2 * M ∧
          N < r - k.val ∧ r - k.val ≤ N' then 1 else 0

/-- The product of the two blocks, regrouped by additive-convolution centre. -/
theorem mvCoefficientBlockSum_mul_mvPhaseBlockSum
    {K M N N' : ℕ} (hmax : 2 * M + N' < K)
    (c : Fin K → ℂ) (d : ℕ → ℂ) :
    mvCoefficientBlockSum K M c * mvPhaseBlockSum K N N' d =
      ∑ r ∈ Finset.Ioc (M + N) (2 * M + N'),
        mvConvolutionSlice K M N N' r c d := by
  classical
  let s : Finset (Fin K × Fin K) :=
    (Finset.univ.product Finset.univ).filter fun q =>
      M < q.1.val ∧ q.1.val ≤ 2 * M ∧ N < q.2.val ∧ q.2.val ≤ N'
  let t : Finset ℕ := Finset.Ioc (M + N) (2 * M + N')
  let g : Fin K × Fin K → ℕ := fun q => q.1.val + q.2.val
  have hmaps : ∀ q ∈ s, g q ∈ t := by
    intro q hq
    simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq
    change g q ∈ Finset.Ioc (M + N) (2 * M + N')
    rw [Finset.mem_Ioc]
    dsimp [g]
    omega
  have hproduct : mvCoefficientBlockSum K M c * mvPhaseBlockSum K N N' d =
      ∑ q ∈ s, c q.1 * d q.2.val := by
    unfold mvCoefficientBlockSum mvPhaseBlockSum
    rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    change (∑ q : Fin K × Fin K,
        (c q.1 * if M < q.1.val ∧ q.1.val ≤ 2 * M then 1 else 0) *
          (d q.2.val * if N < q.2.val ∧ q.2.val ≤ N' then 1 else 0)) =
      ∑ q ∈ (Finset.univ : Finset (Fin K × Fin K)).filter (fun q =>
        M < q.1.val ∧ q.1.val ≤ 2 * M ∧ N < q.2.val ∧ q.2.val ≤ N'),
        c q.1 * d q.2.val
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : M < q.1.val ∧ q.1.val ≤ 2 * M ∧
        N < q.2.val ∧ q.2.val ≤ N'
    · rw [if_pos hq, if_pos ⟨hq.1, hq.2.1⟩,
        if_pos ⟨hq.2.2.1, hq.2.2.2⟩]
      ring
    · rw [if_neg hq]
      by_cases hk : M < q.1.val ∧ q.1.val ≤ 2 * M
      · rw [if_pos hk, if_neg (fun hn => hq ⟨hk.1, hk.2, hn.1, hn.2⟩)]
        ring
      · rw [if_neg hk]
        ring
  rw [hproduct, ← Finset.sum_fiberwise_of_maps_to hmaps]
  change (∑ r ∈ Finset.Ioc (M + N) (2 * M + N'),
      ∑ q ∈ s.filter (fun q => g q = r), c q.1 * d q.2.val) = _
  apply Finset.sum_congr rfl
  intro r hr
  change (∑ q ∈ s.filter (fun q => g q = r), c q.1 * d q.2.val) =
    mvConvolutionSlice K M N N' r c d
  unfold mvConvolutionSlice
  let U : Finset (Fin K) := (Finset.univ : Finset (Fin K)).filter fun k =>
    M < k.val ∧ k.val ≤ 2 * M ∧
      N < r - k.val ∧ r - k.val ≤ N'
  have hK : 0 < K := by omega
  let liftK : ℕ → Fin K := fun n => ⟨n % K, Nat.mod_lt n hK⟩
  have hrightEq : (∑ k : Fin K,
      c k * d (r - k.val) *
        if M < k.val ∧ k.val ≤ 2 * M ∧
            N < r - k.val ∧ r - k.val ≤ N' then 1 else 0) =
      ∑ k ∈ U, c k * d (r - k.val) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkU : k ∈ U
    · have hb : M < k.val ∧ k.val ≤ 2 * M ∧
          N < r - k.val ∧ r - k.val ≤ N' := by
        simpa [U] using hkU
      rw [if_pos hb, if_pos hb, mul_one]
    · have hb : ¬(M < k.val ∧ k.val ≤ 2 * M ∧
          N < r - k.val ∧ r - k.val ≤ N') := by
        intro hb
        apply hkU
        simpa [U] using hb
      rw [if_neg hb, if_neg hb, mul_zero]
  have hfibreEq : s.filter (fun q => g q = r) =
      U.image fun k => (k, liftK (r - k.val)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hq
      have hs := hq.1
      have hs' : M < q.1.val ∧ q.1.val ≤ 2 * M ∧
          N < q.2.val ∧ q.2.val ≤ N' := by simpa [s] using hs
      have hqsum : q.1.val + q.2.val = r := hq.2
      have hidx : q.1.val ≤ r ∧ r - q.1.val < K := by omega
      refine ⟨q.1, ?_, ?_⟩
      · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hs'.1, hs'.2.1, by omega, by omega⟩
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          dsimp [liftK]
          rw [Nat.mod_eq_of_lt hidx.2]
          omega
    · rintro ⟨k, hk, rfl⟩
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      constructor
      · have hs' : M < k.val ∧ k.val ≤ 2 * M ∧
            N < (liftK (r - k.val)).val ∧ (liftK (r - k.val)).val ≤ N' := by
          have hsubK : r - k.val < K := by omega
          have hlift : (liftK (r - k.val)).val = r - k.val := by
            dsimp [liftK]
            rw [Nat.mod_eq_of_lt hsubK]
          rw [hlift]
          exact ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩
        simpa [s] using hs'
      · dsimp [g]
        have hsubK : r - k.val < K := by omega
        dsimp [liftK]
        rw [Nat.mod_eq_of_lt hsubK]
        omega
  rw [hrightEq, hfibreEq, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hsubK : r - k.val < K := by omega
    dsimp [liftK]
    rw [Nat.mod_eq_of_lt hsubK]
  · intro a ha b hb hab
    exact congrArg Prod.fst hab

def mvConvolutionLower (M N' r : ℕ) : ℕ :=
  max M (r - N' - 1)

def mvConvolutionUpper (M N r : ℕ) : ℕ :=
  min (2 * M) (r - N - 1)

def mvConvolutionCoefficient
    (K r : ℕ) (c : Fin K → ℂ) (d : ℕ → ℂ) (k : Fin K) : ℂ :=
  c k * d (r - k.val)

theorem mvConvolution_interval_geometry
    {K M N N' r : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (hNN' : N < N') (hN' : N' ≤ 2 * N)
    (hmax : 2 * M + N' < K)
    (hr : r ∈ Finset.Ioc (M + N) (2 * M + N')) :
    let Y := mvConvolutionLower M N' r
    let Z := mvConvolutionUpper M N r
    Y ≤ Z ∧ Y < K ∧ Z - Y ≤ M ∧ M ≤ Y ∧ Z + M ≤ K := by
  simp only [Finset.mem_Ioc] at hr
  unfold mvConvolutionLower mvConvolutionUpper
  omega

theorem mvConvolutionSlice_eq_interval
    {K M N N' r : ℕ} (hMN : M ≤ N)
    (hr : r ∈ Finset.Ioc (M + N) (2 * M + N'))
    (c : Fin K → ℂ) (d : ℕ → ℂ) :
    mvConvolutionSlice K M N N' r c d =
      mvIntervalCoefficientSum K (mvConvolutionCoefficient K r c d)
        (mvConvolutionLower M N' r) (mvConvolutionUpper M N r) := by
  unfold mvConvolutionSlice mvIntervalCoefficientSum mvConvolutionCoefficient
    mvConvolutionLower mvConvolutionUpper
  apply Finset.sum_congr rfl
  intro k _
  have hrange := Finset.mem_Ioc.mp hr
  by_cases hb : M < k.val ∧ k.val ≤ 2 * M ∧
      N < r - k.val ∧ r - k.val ≤ N'
  · have hi : max M (r - N' - 1) < k.val ∧
        k.val ≤ min (2 * M) (r - N - 1) := by omega
    rw [if_pos hb, if_pos hi]
  · have hi : ¬(max M (r - N' - 1) < k.val ∧
        k.val ≤ min (2 * M) (r - N - 1)) := by
      intro hi
      apply hb
      omega
    rw [if_neg hb, if_neg hi]

theorem norm_mvConvolutionCoefficient_le
    {K Q r : ℕ} (c : Fin K → ℂ) (d : ℕ → ℂ)
    (hc : ∀ k : Fin K, ‖c k‖ ≤ mvBalancedDivisorCount Q k.val)
    (hd : ∀ n : ℕ, ‖d n‖ ≤ 1) (k : Fin K) :
    ‖mvConvolutionCoefficient K r c d k‖ ≤ mvBalancedDivisorCount Q k.val := by
  unfold mvConvolutionCoefficient
  rw [norm_mul]
  have hcount : (0 : ℝ) ≤ mvBalancedDivisorCount Q k.val := by positivity
  calc
    ‖c k‖ * ‖d (r - k.val)‖ ≤
        (mvBalancedDivisorCount Q k.val : ℝ) * 1 :=
      mul_le_mul (hc k) (hd _) (norm_nonneg _) hcount
    _ = mvBalancedDivisorCount Q k.val := mul_one _

theorem mvTrigSum_convolutionCoefficient
    (K r : ℕ) (c : Fin K → ℂ) (d : ℕ → ℂ) (β : ℝ) :
    mvTrigSum K (mvConvolutionCoefficient K r c d) β =
      ∑ k : Fin K, c k * d (r - k.val) * finitePhaseChar ((k.val : ℝ) * β) := by
  unfold mvTrigSum mvConvolutionCoefficient
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Montgomery--Vaughan Lemma 24.10, finite explicit form.** -/
theorem norm_mvCoefficientBlockSum_mul_mvPhaseBlockSum_le
    {K Q M N N' : ℕ} (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hMN : M ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    (hmax : 2 * M + N' < K)
    (c : Fin K → ℂ) (d : ℕ → ℂ)
    (hc : ∀ k : Fin K, ‖c k‖ ≤ mvBalancedDivisorCount Q k.val)
    (hd : ∀ n : ℕ, ‖d n‖ ≤ 1)
    {S : ℝ} (hS : 0 ≤ S) (hSM : S ≤ M)
    (hfull : ∀ r ∈ Finset.Ioc (M + N) (2 * M + N'), ∀ β : ℝ,
      ‖∑ k : Fin K,
          c k * d (r - k.val) * finitePhaseChar ((k.val : ℝ) * β)‖ ≤ S) :
    ‖mvCoefficientBlockSum K M c * mvPhaseBlockSum K N N' d‖ ≤
      (M + N' : ℝ) *
        (7 * Real.sqrt ((M : ℝ) * S) + 3 * Q + 7) := by
  rw [mvCoefficientBlockSum_mul_mvPhaseBlockSum hmax]
  calc
    _ ≤ ∑ r ∈ Finset.Ioc (M + N) (2 * M + N'),
        ‖mvConvolutionSlice K M N N' r c d‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.Ioc (M + N) (2 * M + N'),
        (7 * Real.sqrt ((M : ℝ) * S) + 3 * Q + 7) := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hYZ, hYK, hwidth, hMY, hZK⟩ :=
        mvConvolution_interval_geometry hM hMN hNN' hN' hmax hr
      rw [mvConvolutionSlice_eq_interval hMN hr]
      apply norm_mvIntervalCoefficientSum_le_sqrt_all hQ hM hYZ hYK
        hwidth hMY hZK
      · exact norm_mvConvolutionCoefficient_le c d hc hd
      · exact hS
      · exact hSM
      · intro β
        rw [mvTrigSum_convolutionCoefficient]
        exact hfull r hr β
    _ = ((Finset.Ioc (M + N) (2 * M + N')).card : ℝ) *
        (7 * Real.sqrt ((M : ℝ) * S) + 3 * Q + 7) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M + N' : ℝ) *
        (7 * Real.sqrt ((M : ℝ) * S) + 3 * Q + 7) := by
      have hcard : (Finset.Ioc (M + N) (2 * M + N')).card ≤ M + N' := by
        rw [Nat.card_Ioc]
        omega
      have hcardReal : (((Finset.Ioc (M + N) (2 * M + N')).card : ℕ) : ℝ) ≤
          (M + N' : ℕ) := by exact_mod_cast hcard
      have hfactor : 0 ≤ 7 * Real.sqrt ((M : ℝ) * S) + 3 * Q + 7 := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right hcardReal hfactor
      push_cast at hmul ⊢
      exact hmul

def routeTUpperHalfProductNat (Q : ℕ) (p : Fin Q × Fin Q) : ℕ :=
  (Q + p.1.val) * (Q + p.2.val)

def routeTUpperHalfProductIndex
    {K Q : ℕ} (hK : 4 * Q ^ 2 < K) (p : Fin Q × Fin Q) : Fin K :=
  ⟨routeTUpperHalfProductNat Q p, by
    unfold routeTUpperHalfProductNat
    have h₁ : Q + p.1.val < 2 * Q := by omega
    have h₂ : Q + p.2.val < 2 * Q := by omega
    nlinarith⟩

def routeTProductMultiplicity
    {K Q : ℕ} (hK : 4 * Q ^ 2 < K) (n : Fin K) : ℂ :=
  Fintype.card {p : Fin Q × Fin Q // routeTUpperHalfProductIndex hK p = n}

/-- A rectangular family of products lying strictly inside the receiver block
`Q² < lm ≤ 2Q²`.  Shifting the first coordinate by one avoids the lower endpoint. -/
def routeTProductLowerBox
    {Q : ℕ} (hQ : 8 ≤ Q) (p : Fin (Q / 4) × Fin (Q / 4)) : Fin Q × Fin Q :=
  (⟨p.1.val + 1, by have := p.1.isLt; omega⟩,
    ⟨p.2.val, by have := p.2.isLt; omega⟩)

theorem routeTProductLowerBox_mem
    {Q : ℕ} (hQ : 8 ≤ Q) (p : Fin (Q / 4) × Fin (Q / 4)) :
    Q ^ 2 < routeTUpperHalfProductNat Q (routeTProductLowerBox hQ p) ∧
      routeTUpperHalfProductNat Q (routeTProductLowerBox hQ p) ≤ 2 * Q ^ 2 := by
  have ha := p.1.isLt
  have hb := p.2.isLt
  have ha4 : 4 * (p.1.val + 1) ≤ Q := by omega
  have hb4 : 4 * p.2.val ≤ Q := by omega
  unfold routeTUpperHalfProductNat routeTProductLowerBox
  constructor <;> dsimp
  · nlinarith
  · have hleft : 4 * (Q + (p.1.val + 1)) ≤ 5 * Q := by omega
    have hright : 4 * (Q + p.2.val) ≤ 5 * Q := by omega
    nlinarith [sq_nonneg (Q : ℤ)]

theorem routeTProductLowerBox_injective
    {Q : ℕ} (hQ : 8 ≤ Q) : Function.Injective (routeTProductLowerBox hQ) := by
  intro p q hpq
  apply Prod.ext
  · apply Fin.ext
    have := congrArg (fun z : Fin Q × Fin Q => z.1.val) hpq
    dsimp [routeTProductLowerBox] at this
    omega
  · apply Fin.ext
    exact congrArg (fun z : Fin Q × Fin Q => z.2.val) hpq

theorem norm_routeTProductMultiplicity_le
    {K Q : ℕ} (hQ : 1 ≤ Q) (hK : 4 * Q ^ 2 < K) (n : Fin K) :
    ‖routeTProductMultiplicity hK n‖ ≤ mvBalancedDivisorCount Q n.val := by
  classical
  let F := {p : Fin Q × Fin Q // routeTUpperHalfProductIndex hK p = n}
  let D := (Finset.Icc Q (2 * Q)).filter fun d => d ∣ n.val
  have hmaps : ∀ p ∈ (Finset.univ : Finset F), Q + p.val.1.val ∈ D := by
    intro p _
    simp only [D, Finset.mem_filter, Finset.mem_Icc]
    have hpval := congrArg Fin.val p.property
    unfold routeTUpperHalfProductIndex routeTUpperHalfProductNat at hpval
    exact ⟨⟨by omega, by omega⟩,
      ⟨Q + p.val.2.val, by simpa using hpval.symm⟩⟩
  have hinj : Set.InjOn (fun p : F => Q + p.val.1.val)
      (Finset.univ : Finset F) := by
    intro p _ q _ hpq
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact Nat.add_left_cancel hpq
    · apply Fin.ext
      have hp := congrArg Fin.val p.property
      have hq := congrArg Fin.val q.property
      unfold routeTUpperHalfProductIndex routeTUpperHalfProductNat at hp hq
      have hfirst : Q + p.val.1.val = Q + q.val.1.val := by omega
      have hpos : 0 < Q + p.val.1.val := by omega
      nlinarith
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  unfold routeTProductMultiplicity mvBalancedDivisorCount
  rw [Complex.norm_natCast]
  exact_mod_cast hcard

theorem mvTrigSum_routeTProductMultiplicity
    {K Q : ℕ} (hK : 4 * Q ^ 2 < K) (w : Fin K → ℂ) :
    (∑ p : Fin Q × Fin Q, w (routeTUpperHalfProductIndex hK p)) =
      ∑ n : Fin K, routeTProductMultiplicity hK n * w n := by
  exact sum_comp_eq_sum_card_fiber_mul_complex
    (routeTUpperHalfProductIndex hK) w

/-- Route T's product multiplicity has unconditional mass in the receiver block. -/
theorem routeTProductMultiplicity_block_lower
    {K Q : ℕ} (hQ : 8 ≤ Q) (hK : 4 * Q ^ 2 < K) :
    ((Q : ℝ) ^ 2) / 64 ≤
      ‖mvCoefficientBlockSum K (Q ^ 2) (routeTProductMultiplicity hK)‖ := by
  classical
  let good : Finset (Fin Q × Fin Q) :=
    Finset.univ.filter fun p =>
      Q ^ 2 < routeTUpperHalfProductNat Q p ∧
        routeTUpperHalfProductNat Q p ≤ 2 * Q ^ 2
  have hmaps : ∀ p ∈ (Finset.univ : Finset (Fin (Q / 4) × Fin (Q / 4))),
      routeTProductLowerBox hQ p ∈ good := by
    intro p _
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact routeTProductLowerBox_mem hQ p
  have hinj : Set.InjOn (routeTProductLowerBox hQ)
      (Finset.univ : Finset (Fin (Q / 4) × Fin (Q / 4))) :=
    (routeTProductLowerBox_injective hQ).injOn
  have hcard : (Q / 4) ^ 2 ≤ good.card := by
    have h := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa [Fintype.card_prod, Fintype.card_fin, pow_two] using h
  have hblock : mvCoefficientBlockSum K (Q ^ 2) (routeTProductMultiplicity hK) =
      (good.card : ℂ) := by
    unfold mvCoefficientBlockSum
    rw [← mvTrigSum_routeTProductMultiplicity hK]
    change (∑ p : Fin Q × Fin Q,
        if Q ^ 2 < (routeTUpperHalfProductIndex hK p).val ∧
            (routeTUpperHalfProductIndex hK p).val ≤ 2 * Q ^ 2 then 1 else 0) = _
    rw [← Finset.sum_filter]
    simp only [good, routeTUpperHalfProductIndex, Finset.sum_const, nsmul_eq_mul,
      mul_one, Nat.cast_ofNat]
  rw [hblock, Complex.norm_natCast]
  have hdiv : Q ≤ 8 * (Q / 4) := by omega
  have hrealCard : (((Q / 4) ^ 2 : ℕ) : ℝ) ≤ good.card := by
    exact_mod_cast hcard
  have hq : (0 : ℝ) ≤ Q := by positivity
  have hdivReal : (Q : ℝ) ≤ 8 * (Q / 4 : ℕ) := by exact_mod_cast hdiv
  calc
    ((Q : ℝ) ^ 2) / 64 ≤ (((Q / 4 : ℕ) : ℝ) ^ 2) := by nlinarith
    _ = (((Q / 4) ^ 2 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ good.card := hrealCard

theorem routeTProductMultiplicity_twistedLog_eq
    {K Q : ℕ} (hK : 4 * Q ^ 2 < K) {t x β : ℝ}
    (hx : (4 * Q ^ 2 : ℕ) < x) :
    ∑ n : Fin K, routeTProductMultiplicity hK n *
        finitePhaseChar (t / (2 * Real.pi) * Real.log (x - n.val) + β * n.val) =
      routeTLogTwistedShiftBilinearSum t x β Q := by
  rw [← mvTrigSum_routeTProductMultiplicity hK]
  unfold routeTLogTwistedShiftBilinearSum
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  unfold routeTUpperHalfProductIndex routeTUpperHalfProductNat
    vinogradovUpperHalfProduct
  push_cast
  rfl

theorem mvTrigSum_routeTLogConvolution_eq
    {K Q r : ℕ} (hK : 4 * Q ^ 2 < K) {t β : ℝ}
    (hr : 4 * Q ^ 2 < r) :
    mvTrigSum K
        (mvConvolutionCoefficient K r
          (routeTProductMultiplicity hK)
          (fun n => finitePhaseChar (t / (2 * Real.pi) * Real.log n))) β =
      routeTLogTwistedShiftBilinearSum t r β Q := by
  unfold mvTrigSum mvConvolutionCoefficient
  have hassoc : (∑ n : Fin K,
      routeTProductMultiplicity hK n *
          finitePhaseChar (t / (2 * Real.pi) * Real.log (((r - n.val : ℕ) : ℝ))) *
        finitePhaseChar ((n.val : ℝ) * β)) =
      ∑ n : Fin K, routeTProductMultiplicity hK n *
        (finitePhaseChar (t / (2 * Real.pi) * Real.log (((r - n.val : ℕ) : ℝ))) *
          finitePhaseChar ((n.val : ℝ) * β)) := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hassoc]
  rw [← mvTrigSum_routeTProductMultiplicity hK]
  unfold routeTLogTwistedShiftBilinearSum
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro p _
  have hprod : routeTUpperHalfProductNat Q p < 4 * Q ^ 2 := by
    unfold routeTUpperHalfProductNat
    have h₁ : Q + p.1.val < 2 * Q := by omega
    have h₂ : Q + p.2.val < 2 * Q := by omega
    nlinarith
  have hprodR : routeTUpperHalfProductNat Q p < r := hprod.trans hr
  calc
    finitePhaseChar
          (t / (2 * Real.pi) *
              Real.log (((r - (routeTUpperHalfProductIndex hK p).val : ℕ) : ℝ))) *
        finitePhaseChar (((routeTUpperHalfProductIndex hK p).val : ℝ) * β) =
      finitePhaseChar
        (t / (2 * Real.pi) *
            Real.log (((r - (routeTUpperHalfProductIndex hK p).val : ℕ) : ℝ)) +
          ((routeTUpperHalfProductIndex hK p).val : ℝ) * β) := by
      rw [finitePhaseChar_add]
    _ = finitePhaseChar
        (t / (2 * Real.pi) *
            Real.log (r - vinogradovUpperHalfProduct Q p.1 p.2) +
          β * vinogradovUpperHalfProduct Q p.1 p.2) := by
      congr 1
      have hval : (routeTUpperHalfProductIndex hK p).val =
          routeTUpperHalfProductNat Q p := rfl
      rw [hval]
      rw [Nat.cast_sub (le_of_lt hprodR)]
      unfold routeTUpperHalfProductNat vinogradovUpperHalfProduct
      push_cast
      ring

end

end RHTower.Sieve
