import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.UniformDiscrepancyOfFloorWindows

/-!
# Testing the homogenized floor row against a modulus of continuity

A moving average over K sites changes an observable by at most its
oscillation on K sites. The averaged observable changes by at most
that oscillation divided by K per step. Summation by parts then gives
a uniform weak approximation to half the peak for every translate.
-/

noncomputable section
open Finset GaloisForLFunctions.ArithmeticKreinLangerTheory
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

private def smooth (f : ℕ → ℝ) (K i : ℕ) : ℝ := (∑ j ∈ range K, f (i+j))/(K:ℝ)

private theorem smooth_step (f : ℕ → ℝ) (K i : ℕ) :
    smooth f K (i+1)-smooth f K i = (f (i+K)-f i)/(K:ℝ) := by
  unfold smooth
  rw [←sub_div]
  have he := sum_range_succ' (fun j => f (i+j)) K
  rw [Finset.sum_range_succ] at he
  have hshift : (∑ j ∈ range K, f (i+(j+1))) = ∑ j ∈ range K, f (i+1+j) :=
    sum_congr rfl fun j _ => congrArg f (by omega)
  rw [hshift] at he
  change (∑ j ∈ range K, f (i+j)) + f (i+K) = (∑ j ∈ range K, f (i+1+j)) + f i at he
  congr 1
  linarith only [he]

private theorem sum_bound {a : ℕ → ℝ} {N : ℕ} {c : ℝ} (h : ∀ i < N, |a i| ≤ c) :
    |∑ i ∈ range N, a i| ≤ N*c := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  simpa only [sum_const,card_range,nsmul_eq_mul] using
    sum_le_sum (s:=range N) (fun i hi => h i (mem_range.mp hi))

private theorem abel_window (g b : ℕ → ℝ) (L : ℕ) :
    (∑ i ∈ range L, g i*b i) = (∑ i ∈ range L, g i)*b L +
      ∑ i ∈ range L, (∑ j ∈ range (i+1), g j)*(b i-b (i+1)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ (f:=fun i => g i*b i),ih,sum_range_succ (f:=fun i =>
      (∑ j ∈ range (i+1), g j)*(b i-b (i+1))),sum_range_succ (f:=g)]
    ring

/-- Every bounded observable whose oscillation on K successive steps is
at most D has an explicit uniform error against the constant floor density. -/
theorem floor_window_modulus {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : 0 < K) (hA : AlphabetLE c K) (n L : ℕ) (f : ℕ → ℝ) {M D : ℝ}
    (hM : ∀ i, |f i| ≤ M) (hD : ∀ i j, j ≤ K → |f (i+j)-f i| ≤ D) :
    |∑ i ∈ range L, ((stepWeight c (n+i):ℝ)-(peak c:ℝ)/2)*f i| ≤
      16*K*(peak c:ℝ)*M+(33/2:ℝ)*L*(peak c:ℝ)*D := by
  let w : ℝ := peak c
  let g (i : ℕ) := (stepWeight c (n+i):ℝ)-w/2
  let b := smooth f K
  let C := 16*(K:ℝ)*w
  have hk : 0 < (K:ℝ) := Nat.cast_pos.mpr hK
  have hw : 0 ≤ w := by dsimp only [w]; exact_mod_cast (hP.nonneg 0).trans (hP.stepWeight_le_peak _)
  have hD₀ : 0 ≤ D := by simpa using hD 0 0 (Nat.zero_le _)
  have hM₀ := (abs_nonneg _).trans (hM 0)
  have hC : 0 ≤ C := mul_nonneg (by positivity) hw
  have hprefix (j : ℕ) : |∑ i ∈ range j, g i| ≤ C := by
    have h := floor_window_discrepancy_le hP hK hA n j
    simpa only [g,w,C,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,←mul_div_assoc] using h
  have hg (i : ℕ) : |g i| ≤ w/2 := by
    have h₀ : 0 ≤ (stepWeight c (n+i):ℝ) := by exact_mod_cast hP.nonneg _
    have h₁ : (stepWeight c (n+i):ℝ) ≤ w := by dsimp only [w]; exact_mod_cast hP.stepWeight_le_peak (n+i)
    exact abs_le.mpr ⟨by dsimp only [g]; linarith only [h₀],by dsimp only [g]; linarith only [h₁]⟩
  have hb (i : ℕ) : |b i| ≤ M := by
    change |(∑ j ∈ range K, f (i+j))/(K:ℝ)| ≤ M
    rw [abs_div,abs_of_pos hk,div_le_iff₀ hk,mul_comm M]
    exact sum_bound fun j _ => hM (i+j)
  have herr (i : ℕ) : |f i-b i| ≤ D := by
    have he : f i-b i = (∑ j ∈ range K, (f i-f (i+j)))/(K:ℝ) := by
      rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
      dsimp only [b,smooth]
      field_simp
    rw [he,abs_div,abs_of_pos hk,div_le_iff₀ hk,mul_comm D]
    exact sum_bound fun j hj => (abs_sub_comm _ _).le.trans (hD i j hj.le)
  have hstep (i : ℕ) : |b i-b (i+1)| ≤ D/K := by
    rw [abs_sub_comm,smooth_step,abs_div,abs_of_pos hk]
    exact div_le_div_of_nonneg_right (hD i K le_rfl) hk.le
  have hrest : |∑ i ∈ range L, g i*(f i-b i)| ≤ L*(w/2*D) :=
    sum_bound fun i _ => (abs_mul ..).le.trans (mul_le_mul (hg i) (herr i) (abs_nonneg _) (by positivity))
  have hsm : |∑ i ∈ range L, g i*b i| ≤ C*M+L*(C*(D/K)) := by
    rw [abel_window]
    refine (abs_add_le ..).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (hprefix L) (hb L) (abs_nonneg _) hC
    · exact sum_bound fun i _ => (abs_mul ..).le.trans
        (mul_le_mul (hprefix (i+1)) (hstep i) (abs_nonneg _) hC)
  have he : (∑ i ∈ range L, g i*f i) = (∑ i ∈ range L, g i*b i) +
      ∑ i ∈ range L, g i*(f i-b i) := by
    rw [←sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
  change |∑ i ∈ range L, g i*f i| ≤ _
  rw [he]
  have h := (abs_add_le ..).trans (add_le_add hsm hrest)
  have hc : C*(D/K)=16*w*D := by dsimp only [C]; field_simp
  rw [hc] at h
  exact h.trans_eq (by dsimp only [C,w]; ring)

/-- On the mesh 1/L, a Hölder observable of exponent s has normalized
error of order (K/L)^s plus the boundary error K/L. -/
theorem floor_window_holder {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : 0 < K) (hA : AlphabetLE c K) (n : ℕ) {L : ℕ} (hL : 0 < L)
    (F : ℝ → ℝ) {M A s : ℝ} (hM : ∀ x, |F x| ≤ M) (hA₀ : 0 ≤ A) (hs : 0 ≤ s)
    (hF : ∀ x y, |F x-F y| ≤ A*|x-y|^s) :
    |(∑ i ∈ range L, ((stepWeight c (n+i):ℝ)-(peak c:ℝ)/2)*F ((i:ℝ)/L))/(L:ℝ)| ≤
      (peak c:ℝ)*(16*M*((K:ℝ)/L)+(33/2:ℝ)*A*((K:ℝ)/L)^s) := by
  have hl : 0 < (L:ℝ) := Nat.cast_pos.mpr hL
  have h := floor_window_modulus hP hK hA n L (fun i => F ((i:ℝ)/L)) (fun i => hM _) (D:=A*((K:ℝ)/L)^s) (by
    intro i j hj
    have h := hF (((i+j:ℕ):ℝ)/L) ((i:ℝ)/L)
    rw [Nat.cast_add,add_div,add_sub_cancel_left,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hl.le)] at h
    rw [Nat.cast_add,add_div]
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hj) hl.le) hs) hA₀))
  rw [abs_div,abs_of_pos hl,div_le_iff₀ hl]
  refine h.trans_eq ?_
  field_simp
  <;> ring


end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
