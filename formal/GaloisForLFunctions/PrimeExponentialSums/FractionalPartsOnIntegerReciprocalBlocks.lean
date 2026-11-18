import GaloisForLFunctions.HTGeometry.SmoothedSawtoothFourier
import GaloisForLFunctions.RHTower.DivisorTerminalModularMean

/-!
# Centered fractional parts on sharp integer reciprocal blocks

The second derivative test bounds the nonzero harmonics by a multiple
of the square root of the frequency. Smoothing the sawtooth sums these
bounds with an inverse first power of the smoothing width.
-/

noncomputable section
open Finset
open GaloisForLFunctions.HTGeometry.SmoothedSawtooth
namespace GaloisForLFunctions.PrimeExponentialSums

/-- With square-root growth of the harmonics, the two smoothed sawtooth
coefficient sequences have the same summable majorant off zero. -/
private theorem harmonic_coefficients {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ)
    {a k : ℤ → ℂ}
    (ha : ∀ h : ℤ, ‖a h‖ ≤ A*(1+((h : ℝ)*δ)^2)⁻¹/|(h : ℝ)|)
    (hk : ∀ h : ℤ, ‖k h‖ ≤ A*δ*(1+((h : ℝ)*δ)^2)⁻¹)
    {h : ℤ} (hh : h ≠ 0) :
    ‖a h‖ ≤ A/(δ*|(h : ℝ)|^2) ∧ ‖k h‖ ≤ A/(δ*|(h : ℝ)|^2) := by
  let u := |(h : ℝ)|
  have hu : 0 < u := abs_pos.mpr (by exact_mod_cast hh)
  have ht := mul_pos hu hδ
  have he : ((h : ℝ)*δ)^2 = (u*δ)^2 := by dsimp [u]; rw [mul_pow,mul_pow,sq_abs]
  have h₁ : u*δ ≤ 1+(u*δ)^2 := by nlinarith only [sq_nonneg (u*δ-1/2)]
  constructor
  · apply (ha h).trans
    rw [he]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (inv_anti₀ ht h₁) hA) hu.le).trans_eq
    change A*(u*δ)⁻¹/u=A/(δ*u^2)
    field_simp
  · apply (hk h).trans
    rw [he]
    apply (mul_le_mul_of_nonneg_left (inv_anti₀ (sq_pos_of_pos ht) (le_add_of_nonneg_left zero_le_one))
      (mul_nonneg hA hδ.le)).trans_eq
    change A*δ*((u*δ)^2)⁻¹=A/(δ*u^2)
    field_simp

/-- A smoothing width costs its inverse on nonzero square-root harmonics
and its first power on the unsigned zero harmonic. -/
theorem sawtooth_of_sqrt_harmonics :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type} (s : Finset ι) (y : ι → ℝ) (c : ι → ℂ) (b : ι → ℝ)
      {δ M : ℝ}, 0 < δ → 0 ≤ M → (∀ i, ‖c i‖ ≤ b i) →
      (∀ h : ℤ, h ≠ 0 →
        ‖∑ i ∈ s, c i*fourier h (y i : UnitAddCircle)‖ ≤ M*Real.sqrt |(h : ℝ)| ∧
        ‖∑ i ∈ s, (b i : ℂ)*fourier h (y i : UnitAddCircle)‖ ≤ M*Real.sqrt |(h : ℝ)|) →
      ‖∑ i ∈ s, c i*(saw (y i) : ℂ)‖ ≤ K*(δ*(∑ i ∈ s, b i)+M/δ) := by
  obtain ⟨A,hA,hdec⟩ := exists_saw_decomposition
  let w (h : ℤ) := |(h : ℝ)|^(-(3/2 : ℝ))
  let Z := ∑' h, w h
  have hs : Summable w := Real.summable_abs_int_rpow (by norm_num)
  have hZ : 0 ≤ Z := tsum_nonneg fun h => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨A+2*A*Z,by positivity,?_⟩
  intro ι s y c b δ M hδ hM hb hfreq
  obtain ⟨a,k,haS,hkS,ha,hk,hmain⟩ := hdec δ hδ
  let E (z : ι → ℂ) (h : ℤ) := ‖∑ i ∈ s, z i*fourier h (y i : UnitAddCircle)‖
  let B := ∑ i ∈ s, b i
  have hB : 0 ≤ B := sum_nonneg fun i _ => (norm_nonneg _).trans (hb i)
  let L := A*M/δ
  let G := A*δ*B
  have term (h : ℤ) :
      ‖a h‖*E c h+‖k h‖*E (fun i => (b i : ℂ)) h ≤
        (2*L)*w h+(if h = 0 then G else 0) := by
    rcases eq_or_ne h 0 with rfl | hh
    · have ha₀ : ‖a 0‖ = 0 := le_antisymm (by simpa using ha 0) (norm_nonneg _)
      have hk₀ : ‖k 0‖ ≤ A*δ := by simpa using hk 0
      have he : E (fun i => (b i : ℂ)) 0 = B := by
        simp only [E,fourier_zero,mul_one,←Complex.ofReal_sum,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg hB,B]
      simp only [ha₀,zero_mul,zero_add,he,if_true,w,Int.cast_zero,abs_zero,
        Real.zero_rpow (by norm_num : -(3/2 : ℝ) ≠ 0),mul_zero]
      exact mul_le_mul_of_nonneg_right hk₀ hB
    · obtain ⟨h₁,h₂⟩ := harmonic_coefficients hA hδ ha hk hh
      obtain ⟨h₃,h₄⟩ := hfreq h hh
      have hu : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
      have he : A/(δ*|(h : ℝ)|^2)*(M*Real.sqrt |(h : ℝ)|) = L*w h := by
        have hp : Real.sqrt |(h : ℝ)|/|(h : ℝ)|^2=w h := by
          dsimp only [w]
          rw [show -(3/2 : ℝ) = 1/2-2 by norm_num,Real.rpow_sub hu,Real.rpow_two,←Real.sqrt_eq_rpow]
        rw [←hp]; dsimp [L]; ring
      have hpos : 0 ≤ A/(δ*|(h : ℝ)|^2) := by positivity
      have t₁ := (mul_le_mul h₁ h₃ (norm_nonneg _) hpos).trans_eq he
      have t₂ := (mul_le_mul h₂ h₄ (norm_nonneg _) hpos).trans_eq he
      rw [if_neg hh,add_zero]
      change _ ≤ 2*L*w h
      linarith only [t₁,t₂]
  have s₁ := summable_mul_norm_sum s c y haS
  have s₂ := summable_mul_norm_sum s (fun i => (b i : ℂ)) y hkS
  have sf : Summable fun h : ℤ => if h=0 then G else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun h hh => by rw [mem_singleton] at hh; simp [hh]
  have ht := (s₁.add s₂).tsum_le_tsum term ((hs.mul_left (2*L)).add sf)
  rw [s₁.tsum_add s₂,(hs.mul_left _).tsum_add sf,tsum_mul_left,tsum_ite_eq] at ht
  apply (hmain s y c b hb).trans (ht.trans _)
  change 2*L*Z+G ≤ (A+2*A*Z)*(δ*B+M/δ)
  calc 2*L*Z+G = (2*A*Z)*(M/δ)+A*(δ*B) := by dsimp [L,G]; ring
       _ ≤ (A+2*A*Z)*(M/δ)+(A+2*A*Z)*(δ*B) := add_le_add
         (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (div_nonneg hM hδ.le))
         (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (mul_nonneg hδ.le hB))
       _ = _ := by ring

/-- At a positive harmonic the curvature varies by at most a factor of
eight on a dyadic integer block. Large curvature is covered by its length. -/
private theorem positive_integer_mode {P A B : ℕ} (hP : 1 ≤ P) (hPA : P ≤ A)
    (hAB : A < B) (hBP : B ≤ 2*P) {Z : ℝ} (hZ : 0 < Z) {h : ℤ} (hh : 0 < h) :
    let curvature := 2*Z/(2*(P : ℝ))^3
    ‖∑ t ∈ Ico A B, fourier h ((Z/t : ℝ) : UnitAddCircle)‖ ≤
      (64*P*Real.sqrt curvature + 12/Real.sqrt curvature)*Real.sqrt |(h : ℝ)| := by
  intro curvature
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have ha : (0 : ℝ) < A := hp.trans_le (by exact_mod_cast hPA)
  have hr : (1 : ℝ) ≤ h := by exact_mod_cast (by omega : (1 : ℤ) ≤ h)
  have hr₀ := zero_lt_one.trans_le hr
  have curvature_pos : 0 < curvature := by dsimp [curvature]; positivity
  let N := B-A
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hlen : (N : ℝ) ≤ P := by exact_mod_cast (by dsimp [N]; omega : N ≤ P)
  have hspan : (A : ℝ)+((N-1 : ℕ) : ℝ) ≤ 2*(P : ℝ) := by
    exact_mod_cast (by dsimp [N]; omega : A+(N-1) ≤ 2*P)
  let z (n : ℕ) := Complex.exp (((2*Real.pi*((h : ℝ)*Z/((A : ℝ)+n)) : ℝ) : ℂ)*Complex.I)
  have eqsum : (∑ t ∈ Ico A B, fourier h ((Z/t : ℝ) : UnitAddCircle)) = ∑ n ∈ range N, z n := by
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro n _
    rw [fourier_coe_apply]
    dsimp only [z]
    congr 1
    push_cast
    ring
  have he : 2*((h : ℝ)*Z)/(2*(P : ℝ))^3=(h : ℝ)*curvature := by dsimp [curvature]; ring
  have hbase : ‖∑ n ∈ range N, z n‖ ≤
      64*P*Real.sqrt ((h : ℝ)*curvature)+12/Real.sqrt ((h : ℝ)*curvature) := by
    by_cases hs : (h : ℝ)*curvature ≤ 1
    · have ht := RHTower.norm_reciprocal_phase_sum_le ((h : ℝ)*Z) A (2*(P : ℝ)) N
        (mul_pos hr₀ hZ) ha hn hspan (he.trans_le hs)
      rw [he] at ht
      have hrat : (2*(P : ℝ)/A)^3 ≤ 8 := by
        have h₂ : 2*(P : ℝ)/A ≤ 2 := (div_le_iff₀ ha).mpr
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hPA) (by norm_num))
        exact (pow_le_pow_left₀ (by positivity) h₂ 3).trans_eq (by norm_num)
      have hc := mul_le_mul (mul_le_mul_of_nonneg_left hlen (by norm_num : (0 : ℝ) ≤ 8)) hrat
        (by positivity) (by positivity)
      apply ht.trans
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith only [hc]
    · have ht : ‖∑ n ∈ range N, z n‖ ≤ N := by
        apply (norm_sum_le _ _).trans_eq
        simp only [z,Complex.norm_exp_ofReal_mul_I,sum_const,card_range,nsmul_eq_mul,mul_one]
      have hroot := Real.one_le_sqrt.mpr (le_of_lt (lt_of_not_ge hs))
      have hp' := le_mul_of_one_le_right hp.le hroot
      apply (ht.trans hlen).trans
      nlinarith only [hp',mul_nonneg hp.le (Real.sqrt_nonneg ((h : ℝ)*curvature)),
        div_nonneg (by norm_num : (0 : ℝ) ≤ 12) (Real.sqrt_nonneg ((h : ℝ)*curvature))]
  have hs := Real.one_le_sqrt.mpr hr
  have hinv : 12/(Real.sqrt (h : ℝ)*Real.sqrt curvature) ≤ (12/Real.sqrt curvature)*Real.sqrt (h : ℝ) :=
    (div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr curvature_pos)
      (le_mul_of_one_le_left (Real.sqrt_nonneg _) hs)).trans (le_mul_of_one_le_right (by positivity) hs)
  rw [eqsum,abs_of_pos hr₀]
  rw [Real.sqrt_mul hr₀.le] at hbase
  linarith only [hbase,hinv]

/-- Every nonzero harmonic of the reciprocal phase on a sharp subinterval
is bounded by the square root of the harmonic times the curvature envelope. -/
theorem integer_reciprocal_fourier_block {P A B : ℕ} (hP : 1 ≤ P) (hPA : P ≤ A)
    (hAB : A < B) (hBP : B ≤ 2*P) {Z : ℝ} (hZ : 0 < Z) {h : ℤ} (hh : h ≠ 0) :
    let curvature := 2*Z/(2*(P : ℝ))^3
    ‖∑ t ∈ Ico A B, fourier h ((Z/t : ℝ) : UnitAddCircle)‖ ≤
      (64*P*Real.sqrt curvature+12/Real.sqrt curvature)*Real.sqrt |(h : ℝ)| := by
  rcases lt_or_gt_of_ne hh with hn | hp
  · have ht := positive_integer_mode hP hPA hAB hBP hZ (neg_pos.mpr hn)
    simpa only [fourier_neg,←map_sum,RCLike.norm_conj,Int.cast_neg,abs_neg] using ht
  · exact positive_integer_mode hP hPA hAB hBP hZ hp

/-- Uniform signed discrepancy of reciprocal fractional parts on every
sharp subinterval of a dyadic integer block. -/
theorem centered_fractional_reciprocal_integer_block :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P A B : ℕ}, 1 ≤ P → P ≤ A → A ≤ B → B ≤ 2*P →
      ∀ {Z δ : ℝ}, 0 < Z → 0 < δ →
      let curvature := 2*Z/(2*(P : ℝ))^3
      |∑ t ∈ Ico A B, (Int.fract (Z/t)-1/2)| ≤
        C*(δ*P+(P*Real.sqrt curvature+1/Real.sqrt curvature)/δ) := by
  obtain ⟨K,hK,h⟩ := sawtooth_of_sqrt_harmonics
  refine ⟨64*K,by positivity,?_⟩
  intro P A B hP hPA hAB hBP Z δ hZ hδ curvature
  have curvature_pos : 0 < curvature := by
    have hp : (0 : ℝ) < P := by exact_mod_cast hP
    dsimp [curvature]; positivity
  let M := 64*P*Real.sqrt curvature+12/Real.sqrt curvature
  have hM : 0 ≤ M := by dsimp [M]; positivity
  rcases hAB.eq_or_lt with rfl | hlt
  · simp only [Ico_self,sum_empty,abs_zero]
    positivity
  let S := Ico A B
  let y (t : ℕ) := Z/t
  have mode (h : ℤ) (hh : h ≠ 0) : ‖∑ t ∈ S, fourier h (y t : UnitAddCircle)‖ ≤ M*Real.sqrt |(h : ℝ)| :=
    integer_reciprocal_fourier_block hP hPA hlt hBP hZ hh
  have ht := h S y (fun _ => (1 : ℂ)) (fun _ => (1 : ℝ)) hδ hM (fun _ => by simp) (fun h hh => by
    simpa only [Complex.ofReal_one,one_mul,and_self] using mode h hh)
  have hc : (S.card : ℝ) ≤ P := by exact_mod_cast (show S.card ≤ P by dsimp [S]; rw [Nat.card_Ico]; omega)
  have he : |∑ t ∈ S, (Int.fract (Z/t)-1/2)| ≤ K*(δ*S.card+M/δ) := by
    simpa only [one_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,saw,y,sum_const,nsmul_eq_mul,mul_one] using ht
  apply he.trans
  have hm : M ≤ 64*((P : ℝ)*Real.sqrt curvature+1/Real.sqrt curvature) := by
    dsimp [M]
    simp only [div_eq_mul_inv,one_mul]
    linarith only [inv_nonneg.mpr (Real.sqrt_nonneg curvature)]
  have hb := mul_le_mul_of_nonneg_left hc hδ.le
  have hd := div_le_div_of_nonneg_right hm hδ.le
  apply (mul_le_mul_of_nonneg_left (add_le_add hb hd) hK).trans
  calc _ ≤ K*(64*(δ*P)+64*((P : ℝ)*Real.sqrt curvature+1/Real.sqrt curvature)/δ) := by
          apply mul_le_mul_of_nonneg_left (add_le_add _ le_rfl) hK
          exact le_mul_of_one_le_left (mul_nonneg hδ.le (Nat.cast_nonneg P)) (by norm_num)
       _ = _ := by ring

#print axioms integer_reciprocal_fourier_block
#print axioms centered_fractional_reciprocal_integer_block
end GaloisForLFunctions.PrimeExponentialSums
