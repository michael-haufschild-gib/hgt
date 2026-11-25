import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.HolomorphicSquareMean
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.MollifierTailWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimitiveHybridLargeSieve

/-! Holomorphic sampling of a Möbius detector at heights separated within each character. -/

open Complex Finset MeasureTheory

namespace QH.PrimeProgressions

/-- The tail of the truncated Möbius convolution between Q cubed and Q to the sixth. -/
noncomputable def mollifierTail {q : ℕ} (Q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc (Q ^ 3) (Q ^ 6), mollifierCoeff Q n * χ (n : ZMod q) * (n : ℂ) ^ (-s)

private theorem mollifierTail_differentiable {q : ℕ} (Q : ℕ) (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (mollifierTail Q χ) := by
  intro s
  unfold mollifierTail
  refine DifferentiableAt.fun_sum fun n hn => ?_
  have hn₀ : (n : ℂ) ≠ 0 := by
    exact_mod_cast ((Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1).ne'
  exact (differentiableAt_id.neg.const_cpow (Or.inl hn₀)).const_mul _

private theorem sum_height_windows_le {ι : Type*} (U : Finset ι) (t : ι → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x) {r V : ℝ}
    (hr : 0 < r) (hV : 0 ≤ V)
    (hsep : ∀ i ∈ U, ∀ j ∈ U, i ≠ j → 2 * r ≤ |t i - t j|)
    (hU : ∀ i ∈ U, -V ≤ t i - r ∧ t i + r ≤ V) :
    ∑ i ∈ U, ∫ x in (t i - r)..(t i + r), f x ≤ ∫ x in (-V)..V, f x := by
  have hwin (i : ι) (_ : i ∈ U) :
      (∫ x in (t i - r)..(t i + r), f x) = ∫ x in Set.Ioc (t i - r) (t i + r), f x :=
    intervalIntegral.integral_of_le (by linarith only [hr])
  rw [sum_congr rfl hwin]
  rw [intervalIntegral.integral_of_le (by linarith only [hV]),
    ← integral_biUnion_finset U (fun i _ => measurableSet_Ioc)]
  · refine setIntegral_mono_set hf.integrableOn_Ioc
      (Filter.Eventually.of_forall hnonneg) ?_
    refine (show (⋃ i ∈ U, Set.Ioc (t i - r) (t i + r)) ⊆ Set.Ioc (-V) V from ?_).eventuallyLE
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨(hU i hi).1.trans_lt hxi.1, hxi.2.trans (hU i hi).2⟩
  · intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    rcases le_abs.mp (hsep i hi j hj hij) with h | h
    · linarith only [h, hxi.1, hxj.2]
    · linarith only [h, hxj.1, hxi.2]
  · exact fun _ _ => hf.integrableOn_Ioc

/-- The detector exceeds one half at at most O(Q^(1/8)) separated points across primitive characters. -/
theorem spaced_mollifier_detection_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 2 ≤ Q →
      ∀ U : Finset ((Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ),
      (∀ p ∈ U, p.1.1 + 1 ≤ Q ∧ p.1.2.IsPrimitive ∧
        1 - 1 / 400 ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ Q ∧
        (1 / 2 : ℝ) ≤ ‖mollifierTail Q p.1.2 p.2‖) →
      (∀ p ∈ U, ∀ p' ∈ U, p.1 = p'.1 → p ≠ p' → 1 ≤ |p.2.im - p'.2.im|) →
      (U.card : ℝ) ≤ C * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
  classical
  let A : ℝ := (Real.pi * (1 / 800 : ℝ) ^ 2)⁻¹
  let B : ℝ := 8 * Real.pi * (240 * (RHTower.Sieve.divisorBoundConst (1 / 400)) ^ 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by
    have := RHTower.Sieve.divisorBoundConst_pos (ε := (1 / 400 : ℝ)) (by norm_num)
    dsimp [B]
    positivity
  refine ⟨4 * (A * B), by positivity, ?_⟩
  intro Q hQ U hU hsep
  let r : ℝ := 1 / 800
  let V : ℝ := Q + 1
  let a : ℝ := 1 - 3 / 800
  let b : ℝ := 1 + 1 / 800
  let F (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) := mollifierTail Q x.2
  let G (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (d σ : ℝ) :=
    ∫ t in (d - r)..(d + r), ‖F x (σ + t * I)‖ ^ 2
  let H (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (σ : ℝ) :=
    ∫ t in (-V)..V, ‖F x (σ + t * I)‖ ^ 2
  let P := U.image Prod.fst
  have hV : 1 ≤ V := le_add_of_nonneg_left (Nat.cast_nonneg Q)
  have hab : a ≤ b := by norm_num [a, b]
  have hf (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) : Continuous (F x) :=
    (mollifierTail_differentiable Q x.2).continuous
  have hg (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (d : ℝ) : Continuous (G x d) := by
    unfold G
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have hh (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) : Continuous (H x) := by
    unfold H
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have hsample (p : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ) (hp : p ∈ U) :
      (1 / 4 : ℝ) ≤ A * ∫ σ in a..b, G p.1 p.2.im σ := by
    obtain ⟨_, _, h₁, h₂, _, h₃⟩ := hU p hp
    have hsq : (1 / 4 : ℝ) ≤ ‖F p.1 p.2‖ ^ 2 := by
      change (1 / 2 : ℝ) ≤ ‖F p.1 p.2‖ at h₃
      nlinarith only [h₃, sq_nonneg (‖F p.1 p.2‖ - 1 / 2)]
    refine hsq.trans ((normSq_le_integral_square _ (mollifierTail_differentiable Q p.1.2)
      p.2 (r := r) (by norm_num [r])).trans ?_)
    apply mul_le_mul_of_nonneg_left _ hA.le
    refine intervalIntegral.integral_mono_interval ?_ ?_ ?_ ?_ ((hg _ _).intervalIntegrable _ _)
    · dsimp [a, r]; linarith only [h₁]
    · dsimp [r]; linarith
    · dsimp [b, r]; linarith only [h₂]
    · exact Filter.Eventually.of_forall fun σ =>
        intervalIntegral.integral_nonneg (by dsimp [r]; linarith) fun _ _ => sq_nonneg _
  have hgroup :
      ∑ p ∈ U, (∫ σ in a..b, G p.1 p.2.im σ) ≤
        ∑ x ∈ P, ∫ σ in a..b, H x σ := by
    rw [← sum_fiberwise_of_maps_to (s := U) (t := P) (g := Prod.fst)
      (fun p hp => mem_image_of_mem Prod.fst hp)]
    refine sum_le_sum fun x _ => ?_
    rw [← intervalIntegral.integral_finsetSum (fun p _ => (hg p.1 p.2.im).intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on hab
      ((continuous_finsetSum _ fun p _ => hg p.1 p.2.im).intervalIntegrable _ _)
      ((hh x).intervalIntegrable _ _) fun σ _ => ?_
    have heq (p : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ)
        (hp : p ∈ U.filter (fun p => p.1 = x)) : G p.1 p.2.im σ = G x p.2.im σ := by
      rw [(mem_filter.mp hp).2]
    rw [sum_congr rfl heq]
    refine sum_height_windows_le (r := r) (V := V) (U.filter (fun p => p.1 = x))
      (fun p => p.2.im) (fun t => ‖F x (σ + t * I)‖ ^ 2)
      (by fun_prop) (fun _ => sq_nonneg _) (by norm_num [r])
      (zero_le_one.trans hV) ?_ ?_
    · intro p hp p' hp' hne
      obtain ⟨hpU, hpX⟩ := mem_filter.mp hp
      obtain ⟨hp'U, hp'X⟩ := mem_filter.mp hp'
      exact (by norm_num [r] : 2 * r ≤ 1).trans (hsep p hpU p' hp'U (hpX.trans hp'X.symm) hne)
    · intro p hp
      have ht := abs_le.mp (hU p (mem_filter.mp hp).1).2.2.2.2.1
      dsimp [V, r]
      constructor <;> linarith only [ht.1, ht.2]
  have hsieve (σ : ℝ) (hσ : σ ∈ Set.Icc a b) :
      ∑ x ∈ P, H x σ ≤ B * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
    let S := Ioc (Q ^ 3) (Q ^ 6)
    let c (n : ℕ) := mollifierCoeff Q n * (n : ℂ) ^ (-(σ : ℂ))
    have hnpos (n : ℕ) (hn : n ∈ S) : 0 < n := (Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1
    have hre (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (t : ℝ) :
        F x (σ + t * I) =
          ∑ n ∈ S, c n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I)) := by
      refine sum_congr rfl fun n hn => ?_
      have hn₀ : (n : ℂ) ≠ 0 := by exact_mod_cast (hnpos n hn).ne'
      dsimp [c]
      rw [neg_add, Complex.cpow_add _ _ hn₀]
      ring
    have hsub : P ⊆ (range Q).sigma
        (fun q => univ.filter (DirichletCharacter.IsPrimitive (R := ℂ) (n := q + 1))) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      obtain ⟨hq, hprim, _⟩ := hU p hp
      exact mem_sigma.mpr ⟨mem_range.mpr (by omega), mem_filter.mpr ⟨mem_univ _, hprim⟩⟩
    have hnonneg (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) : 0 ≤ H x σ :=
      intervalIntegral.integral_nonneg (by linarith only [hV]) fun _ _ => sq_nonneg _
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hnonneg x)).trans ?_
    simp only [sum_sigma, H, hre]
    refine (primitive_hybrid_large_sieve hQ hnpos c hV).trans ?_
    dsimp only [B, c, S, V]
    exact (mul_le_mul_of_nonneg_left (mollifier_coeff_energy Q hQ hσ.1)
      (by positivity : (0 : ℝ) ≤ 8 * Real.pi)).trans_eq (by ring)
  have hmean : (∑ x ∈ P, ∫ σ in a..b, H x σ) ≤ B * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← intervalIntegral.integral_finsetSum (fun x _ => (hh x).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ _ in a..b, B * (Q : ℝ) ^ ((1 : ℝ) / 8) :=
        intervalIntegral.integral_mono_on hab
          ((continuous_finsetSum _ fun x _ => hh x).intervalIntegrable _ _) intervalIntegrable_const hsieve
      _ ≤ _ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        exact mul_le_of_le_one_left (by positivity) (by norm_num [a, b])
  have hsum : (U.card : ℝ) * (1 / 4) ≤ A * ∑ p ∈ U, ∫ σ in a..b, G p.1 p.2.im σ := by
    rw [← nsmul_eq_mul, ← sum_const, mul_sum]
    exact sum_le_sum hsample
  calc
    _ = 4 * ((U.card : ℝ) * (1 / 4)) := by ring
    _ ≤ 4 * (A * (B * (Q : ℝ) ^ ((1 : ℝ) / 8))) :=
      mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left (hgroup.trans hmean) hA.le)) (by norm_num)
    _ = _ := by ring

end QH.PrimeProgressions
