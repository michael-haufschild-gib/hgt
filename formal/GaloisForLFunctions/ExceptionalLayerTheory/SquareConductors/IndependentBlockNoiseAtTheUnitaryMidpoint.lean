import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.WalshConstraintsAtTheUnitaryMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RankDefectsAtTheUnitaryMidpoint

/-!
# Independent block noise at the unitary midpoint

The independent birth and death dynamics on prime-power blocks have a
product transition kernel. Their eigenvalues distinguish the degree-one
and higher odd contributions to the arithmetic cut. The slowest possible
decorrelation is attained precisely when one block dominates.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- One-step transition kernel for independent prime-power block flips.
The correlation parameter is one minus twice the flip probability. -/
def primeBlockNoise (P : Finset ℕ) (ρ : ℝ) (A B : Finset ℕ) : ℝ :=
  (∏ p ∈ P, (1 + ρ*((if p ∈ A then -1 else 1 : ℤ):ℝ)*((if p ∈ B then -1 else 1 : ℤ):ℝ))) /
    (2:ℝ)^P.card

/-- The product kernel has the Walsh expansion with an exact power of
the correlation parameter for each rank. -/
theorem primeBlockNoise_spectrum (P : Finset ℕ) (ρ : ℝ) (A B : Finset ℕ) :
    primeBlockNoise P ρ A B =
      (∑ T ∈ P.powerset, ρ^T.card*(blockCharacter T A:ℝ)*(blockCharacter T B:ℝ))/(2:ℝ)^P.card := by
  rw [primeBlockNoise,prod_one_add]
  congr 1
  apply sum_congr rfl
  intro T _
  simp only [prod_mul_distrib,prod_const,blockCharacter,Int.cast_prod]

private theorem real_mode_pair {P T U : Finset ℕ} (hT : T ⊆ P) (hU : U ⊆ P) :
    ∑ A ∈ P.powerset, (blockCharacter T A:ℝ)*(blockCharacter U A:ℝ) =
      if T=U then (2:ℝ)^P.card else 0 := by
  simp_rw [blockCharacter_comm T,blockCharacter_comm U]
  exact_mod_cast blockCharacter_column_orthogonality hT hU

/-- Noise acts diagonally on each Walsh mode at any prime support. -/
theorem primeBlockNoise_character (P : Finset ℕ) (ρ : ℝ) (A : Finset ℕ) {U : Finset ℕ} (hU : U ⊆ P) :
    ∑ B ∈ P.powerset, primeBlockNoise P ρ A B*(blockCharacter U B:ℝ) =
      ρ^U.card*(blockCharacter U A:ℝ) := by
  let n := (2:ℝ)^P.card
  let f (T : Finset ℕ) := ρ^T.card*(blockCharacter T A:ℝ)
  simp_rw [primeBlockNoise_spectrum,div_mul_eq_mul_div,sum_mul]
  rw [← sum_div,sum_comm]
  have term (T : Finset ℕ) (hT : T ∈ P.powerset) :
      ∑ B ∈ P.powerset, f T*(blockCharacter T B:ℝ)*(blockCharacter U B:ℝ) =
        if T=U then f T*n else 0 := by
    simp only [mul_assoc,← mul_sum,real_mode_pair (mem_powerset.mp hT) hU,mul_ite,mul_zero,n]
  change (∑ T ∈ P.powerset, ∑ B ∈ P.powerset, f T*(blockCharacter T B:ℝ)*(blockCharacter U B:ℝ))/n=_
  rw [sum_congr rfl term,sum_ite_eq',if_pos (mem_powerset.mpr hU),mul_div_cancel_right₀ _ (by positivity : n≠0)]

/-- For every actual flip probability the weights are nonnegative and have
unit total mass, even for the empty cube. -/
theorem primeBlockNoise_probability (P : Finset ℕ) {ρ : ℝ} (hρ : |ρ| ≤ 1) (A : Finset ℕ) :
    (∀ B, 0 ≤ primeBlockNoise P ρ A B) ∧ (∑ B ∈ P.powerset, primeBlockNoise P ρ A B) = 1 := by
  refine ⟨fun B => div_nonneg (prod_nonneg fun p _ => ?_) (by positivity),?_⟩
  · have hh := abs_le.mp hρ
    split_ifs <;> push_cast <;> linarith only [hh.1,hh.2]
  · simpa only [blockCharacter,prod_empty,Int.cast_one,mul_one,card_empty,pow_zero] using
      primeBlockNoise_character P ρ A (empty_subset _)

/-- Performing two independent rounds multiplies their correlation
parameters. This holds on every pair of actual cube vertices. -/
theorem primeBlockNoise_comp (P : Finset ℕ) (ρ τ : ℝ) (A C : Finset ℕ) :
    ∑ B ∈ P.powerset, primeBlockNoise P ρ A B*primeBlockNoise P τ B C =
      primeBlockNoise P (ρ*τ) A C := by
  simp_rw [primeBlockNoise_spectrum P τ, mul_div_assoc',mul_sum]
  rw [← sum_div,sum_comm,primeBlockNoise_spectrum]
  congr 1
  refine sum_congr rfl fun T hT => ?_
  have h (B : Finset ℕ) : primeBlockNoise P ρ A B*
      (τ^T.card*(blockCharacter T B:ℝ)*(blockCharacter T C:ℝ)) =
      (primeBlockNoise P ρ A B*(blockCharacter T B:ℝ))*(τ^T.card*(blockCharacter T C:ℝ)) := by ring
  simp_rw [h]
  rw [← sum_mul,primeBlockNoise_character P ρ A (mem_powerset.mp hT),mul_pow]
  ring

/-- The signed cut, with opposite signs on complementary strict sides. -/
def unitaryCutSign (k : ℕ) (A : Finset ℕ) : ℤ :=
  (if A ∈ smallUnitarySubsets k then 1 else 0) -
    (if k.primeFactors \ A ∈ smallUnitarySubsets k then 1 else 0)

private theorem cut_sign_abs {k : ℕ} (hk : 1 < k) {A : Finset ℕ} (ha : A ⊆ k.primeFactors) :
    (unitaryCutSign k A)^2=1 := by
  by_cases h : A ∈ smallUnitarySubsets k <;>
    simp [unitaryCutSign,unitary_complement_mem_small_iff hk ha,h]

/-- Total squared Walsh mass is exactly the square of the cube size for
every nontrivial integer, independently of its prime-block geometry. -/
theorem unitaryWalshContrast_parseval {k : ℕ} (hk : 1 < k) :
    ∑ T ∈ k.primeFactors.powerset, (unitaryWalshContrast k T)^2 = ((2:ℤ)^k.primeFactors.card)^2 := by
  let P := k.primeFactors
  let n := (2:ℤ)^P.card
  let c := unitaryWalshContrast k
  let f (A : Finset ℕ) := ∑ T ∈ P.powerset, c T*blockCharacter T A
  have at_vertex (A : Finset ℕ) (ha : A ∈ P.powerset) : f A = n*unitaryCutSign k A :=
    unitaryWalshContrast_inversion k (mem_powerset.mp ha)
  have hs : ∑ A ∈ P.powerset, (f A)^2 = n*n^2 := by
    have h (A : Finset ℕ) (ha : A ∈ P.powerset) : (f A)^2=n^2 := by
      rw [at_vertex A ha,mul_pow,cut_sign_abs hk (mem_powerset.mp ha),mul_one]
    rw [sum_congr rfl h,sum_const,card_powerset,nsmul_eq_mul]
    push_cast
    rfl
  have expand (A : Finset ℕ) : (f A)^2 = ∑ T ∈ P.powerset, c T*(f A*blockCharacter T A) := by
    calc _ = f A*(∑ T ∈ P.powerset, c T*blockCharacter T A) := sq _
         _ = _ := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  simp_rw [expand] at hs
  rw [sum_comm] at hs
  have term (T : Finset ℕ) (ht : T ∈ P.powerset) :
      ∑ A ∈ P.powerset, c T*(f A*blockCharacter T A) = n*(c T)^2 := by
    rw [← mul_sum,show (∑ A ∈ P.powerset, f A*blockCharacter T A) = c T*n from
      blockCharacter_double_transform (mem_powerset.mp ht) c]
    ring
  rw [sum_congr rfl term,←mul_sum] at hs
  exact mul_left_cancel₀ (pow_ne_zero P.card (by norm_num : (2:ℤ)≠0)) hs

/-- Unnormalized stationary noise correlation of the signed unitary cut.
Division by the square of the cube size gives the correlation coefficient. -/
def unitaryNoiseCorrelation (k : ℕ) (ρ : ℝ) : ℝ :=
  ∑ T ∈ k.primeFactors.powerset, ρ^T.card*(unitaryWalshContrast k T:ℝ)^2

private theorem cut_fourier {k : ℕ} {T : Finset ℕ} (ht : T ⊆ k.primeFactors) :
    ∑ A ∈ k.primeFactors.powerset, unitaryCutSign k A*blockCharacter T A = unitaryWalshContrast k T := by
  let P := k.primeFactors
  let n := (2:ℤ)^P.card
  have h := blockCharacter_double_transform ht (unitaryWalshContrast k)
  have vertex (A : Finset ℕ) (ha : A ∈ P.powerset) :
      (∑ U ∈ P.powerset, unitaryWalshContrast k U*blockCharacter U A)*blockCharacter T A =
        n*(unitaryCutSign k A*blockCharacter T A) := by
    rw [show (∑ U ∈ P.powerset, unitaryWalshContrast k U*blockCharacter U A) = n*unitaryCutSign k A from
        unitaryWalshContrast_inversion k (mem_powerset.mp ha),mul_assoc]
  rw [sum_congr rfl vertex,←mul_sum,mul_comm (unitaryWalshContrast k T)] at h
  exact mul_left_cancel₀ (pow_ne_zero P.card (by norm_num : (2:ℤ)≠0)) h

/-- The spectral quantity is the physical two-point reading of the
independent transition kernel, with the counting normalization explicit. -/
theorem unitaryNoiseCorrelation_physical (k : ℕ) (ρ : ℝ) :
    let P := k.primeFactors
    (∑ A ∈ P.powerset, ∑ B ∈ P.powerset, (unitaryCutSign k A:ℝ)*primeBlockNoise P ρ A B*
      (unitaryCutSign k B:ℝ)) = unitaryNoiseCorrelation k ρ/(2:ℝ)^P.card := by
  intro P
  let f (A : Finset ℕ) : ℝ := unitaryCutSign k A
  let χ (T A : Finset ℕ) : ℝ := blockCharacter T A
  let c (T : Finset ℕ) : ℝ := unitaryWalshContrast k T
  have coef (T : Finset ℕ) (ht : T ∈ P.powerset) : ∑ A ∈ P.powerset, f A*χ T A = c T := by
    dsimp only [f,χ,c]
    exact_mod_cast cut_fourier (mem_powerset.mp ht)
  have inner (A : Finset ℕ) :
      ∑ B ∈ P.powerset, f A*primeBlockNoise P ρ A B*f B =
        (∑ T ∈ P.powerset, (ρ^T.card*c T)*(f A*χ T A))/(2:ℝ)^P.card := by
    simp_rw [primeBlockNoise_spectrum,mul_div_assoc',div_mul_eq_mul_div,mul_sum,sum_mul]
    rw [←sum_div,sum_comm]
    congr 1
    refine sum_congr rfl fun T hT => ?_
    have term (B : Finset ℕ) :
        f A*(ρ^T.card*(blockCharacter T A:ℝ)*(blockCharacter T B:ℝ))*f B =
          (ρ^T.card*(f A*χ T A))*(f B*χ T B) := by dsimp only [χ]; ring
    simp_rw [term]
    rw [←mul_sum,coef T hT]
    ring
  change (∑ A ∈ P.powerset, ∑ B ∈ P.powerset, f A*primeBlockNoise P ρ A B*f B) = _
  simp_rw [inner]
  rw [←sum_div,sum_comm]
  congr 1
  apply sum_congr rfl
  intro T hT
  rw [←mul_sum,coef T hT]
  change ρ^T.card*c T*c T=ρ^T.card*(c T)^2
  ring

/-- Nonlinear odd modes account for the entire departure from linear
decay under independent block noise. -/
theorem unitaryNoiseCorrelation_defect (k : ℕ) (ρ : ℝ) :
    ρ*unitaryNoiseCorrelation k 1-unitaryNoiseCorrelation k ρ =
      ∑ T ∈ nonlinearUnitaryRanks k, (ρ-ρ^T.card)*(unitaryWalshContrast k T:ℝ)^2 := by
  unfold unitaryNoiseCorrelation
  simp only [one_pow,one_mul,mul_sum,←sum_sub_distrib,←sub_mul]
  symm
  apply sum_subset (filter_subset ..)
  intro T hT hf
  rcases Nat.even_or_odd T.card with he|ho
  · simp [unitaryWalshContrast_even (mem_powerset.mp hT) he]
  · have hlt : ¬3 ≤ T.card := fun h => hf (mem_filter.mpr ⟨hT,ho,h⟩)
    obtain ⟨j,hj⟩ := ho
    have h₁ : T.card = 1 := by omega
    simp [h₁]

/-- For a balanced integer, the spectral departure is bounded below by a
quantity depending only on the available ranks, uniformly over prime sizes. -/
theorem balanced_noise_loss {k : ℕ} (hk : 1 < k)
    (hbal : ∀ p ∈ k.primeFactors, (p^k.factorization p)^2 < k) {ρ : ℝ} (hρ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    (ρ-ρ^3)*((2:ℝ)^k.primeFactors.card)^2 ≤
      (∑ T ∈ nonlinearUnitaryRanks k, ((T.card:ℝ)-1)^2) *
        (ρ*unitaryNoiseCorrelation k 1-unitaryNoiseCorrelation k ρ) := by
  let F := nonlinearUnitaryRanks k
  let b (T : Finset ℕ) := (T.card:ℝ)-1
  let c (T : Finset ℕ) : ℝ := unitaryWalshContrast k T
  have hrank : ∑ T ∈ F, b T*c T = -(2:ℝ)^k.primeFactors.card := by
    rw [sum_subset (show F ⊆ k.primeFactors.powerset from filter_subset ..) (fun T hT hf => ?_)]
    · dsimp only [b,c]
      exact_mod_cast unitaryWalshContrast_rank_excess hk hbal
    · rcases Nat.even_or_odd T.card with he|ho
      · simp [c,unitaryWalshContrast_even (mem_powerset.mp hT) he]
      · have hlt : ¬3 ≤ T.card := fun h => hf (mem_filter.mpr ⟨hT,ho,h⟩)
        obtain ⟨j,hj⟩ := ho
        have hh : T.card=1 := by omega
        simp [b,hh]
  have hρ₃ : ρ^3 ≤ ρ := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hρ h₁ (by decide : 1≤3))
  have hsum : (ρ-ρ^3)*∑ T ∈ F, (c T)^2 ≤ ρ*unitaryNoiseCorrelation k 1-unitaryNoiseCorrelation k ρ := by
    rw [unitaryNoiseCorrelation_defect,mul_sum]
    apply sum_le_sum
    intro T hT
    exact mul_le_mul_of_nonneg_right (sub_le_sub_left (pow_le_pow_of_le_one hρ h₁ (mem_filter.mp hT).2.2) ρ) (sq_nonneg _)
  have cs := sum_mul_sq_le_sq_mul_sq F b c
  rw [hrank,neg_sq] at cs
  calc _ ≤ (ρ-ρ^3)*((∑ T ∈ F, (b T)^2)*∑ T ∈ F, (c T)^2) :=
          mul_le_mul_of_nonneg_left cs (sub_nonneg.mpr hρ₃)
       _ = (∑ T ∈ F, (b T)^2)*((ρ-ρ^3)*∑ T ∈ F, (c T)^2) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hsum (sum_nonneg fun _ _ => sq_nonneg _)

/-- Exactly the integers with a dominant block preserve the full linear
correlation at any one strictly intermediate noise level. -/
theorem unitary_noise_linear_iff_dominant {k : ℕ} (hk : 1<k) {ρ : ℝ} (hρ : 0<ρ) (hu : ρ<1) :
    unitaryNoiseCorrelation k ρ = ρ*((2:ℝ)^k.primeFactors.card)^2 ↔
      ∃ p ∈ k.primeFactors, k < (p^k.factorization p)^2 := by
  let P := k.primeFactors
  let F := nonlinearUnitaryRanks k
  let c (T : Finset ℕ) : ℝ := unitaryWalshContrast k T
  let e (T : Finset ℕ) := (ρ-ρ^T.card)*(c T)^2
  have h₁ : unitaryNoiseCorrelation k 1 = ((2:ℝ)^P.card)^2 := by
    simp only [unitaryNoiseCorrelation,one_pow,one_mul]
    exact_mod_cast unitaryWalshContrast_parseval hk
  have positive {T : Finset ℕ} (ht : T ∈ F) : 0 < ρ-ρ^T.card := by
    have hge := (mem_filter.mp ht).2.2
    apply sub_pos.mpr
    simpa only [pow_one] using pow_lt_pow_of_lt_one hρ hu (show 1<T.card by omega)
  constructor
  · intro he
    have hsum : ∑ T ∈ F, e T = 0 := by
      rw [←show ρ*unitaryNoiseCorrelation k 1-unitaryNoiseCorrelation k ρ = ∑ T ∈ F,e T from
        unitaryNoiseCorrelation_defect k ρ,h₁,he,sub_self]
    have hz := (sum_eq_zero_iff_of_nonneg (fun T ht => mul_nonneg (positive ht).le (sq_nonneg (c T)))).mp hsum
    have hE : unitaryVirialEnergy (1/10) k=0 := by
      apply sum_eq_zero
      intro T hT
      rcases Nat.even_or_odd T.card with heven|hodd
      · simp [unitaryWalshContrast_even (mem_powerset.mp hT) heven]
      by_cases hi : 3 ≤ T.card
      · have ht : T ∈ F := mem_filter.mpr ⟨hT,hodd,hi⟩
        have hc := (mul_eq_zero.mp (hz T ht)).resolve_left (positive ht).ne'
        change _*(c T)^2=0
        rw [hc,mul_zero]
      · obtain ⟨j,hj⟩ := hodd
        have hcard : T.card=1 := by omega
        norm_num [hcard,blockVirialSymbol]
    exact ((unitaryVirialEnergy_zero_iff k).mp hE).resolve_left hk.not_ge
  · rintro ⟨p,hp,hbig⟩
    rw [unitaryNoiseCorrelation]
    rw [sum_eq_single {p}]
    · rw [dominant_unitary_single_mode hk hp hbig (singleton_subset_iff.mpr hp)]
      simp
    · intro T hT hne
      rw [dominant_unitary_single_mode hk hp hbig (mem_powerset.mp hT),if_neg hne]
      simp
    · intro hh
      exact (hh (mem_powerset.mpr (singleton_subset_iff.mpr hp))).elim

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
