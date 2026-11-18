import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOnIntegerReciprocalBlocks
import GaloisForLFunctions.RHTower.Sieve.BilinearCauchySchwarz
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiGramSchur

/-!
# Bilinear reciprocal phases on short factor intervals

Two product restrictions intersect in a single interval of the longer
variable. The difference of reciprocal phases is reciprocal again, with
frequency proportional to the gap in the shorter variable.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.PrimeExponentialSums

/-- The harmonic of the reciprocal product on its sharp product interval. -/
def maskedReciprocalProduct (Z : ℝ) (h : ℤ) (L U p m : ℕ) : ℂ :=
  if L < p*m ∧ p*m ≤ U then fourier h ((Z/m/p : ℝ) : UnitAddCircle) else 0

private theorem correlation_exact {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (P L U : ℕ) (Z : ℝ) (h : ℤ) :
    let A := max P (max (L/m+1) (L/n+1))
    let B := min (2*P) (min (U/m+1) (U/n+1))
    (∑ p ∈ Ico P (2*P), maskedReciprocalProduct Z h L U p m*
      (starRingEnd ℂ) (maskedReciprocalProduct Z h L U p n)) =
      ∑ p ∈ Ico A B, fourier h (((Z/m-Z/n)/p : ℝ) : UnitAddCircle) := by
  intro A B
  let inside (p v : ℕ) := L < p*v ∧ p*v ≤ U
  have mem (p v : ℕ) (hv : 1 ≤ v) : inside p v ↔ L/v < p ∧ p ≤ U/v := by
    dsimp [inside]
    rw [Nat.div_lt_iff_lt_mul hv,Nat.le_div_iff_mul_le hv]
  have he : ((Ico P (2*P)).filter fun p => inside p m ∧ inside p n)=Ico A B := by
    ext p
    simp only [mem_filter,mem_Ico,A,B,max_le_iff,lt_min_iff,mem p m hm,mem p n hn]
    omega
  rw [←he,sum_filter]
  apply sum_congr rfl
  intro p _
  change (if inside p m then fourier h ((Z/m/p : ℝ) : UnitAddCircle) else 0) *
    (starRingEnd ℂ) (if inside p n then fourier h ((Z/n/p : ℝ) : UnitAddCircle) else 0) =
    if inside p m ∧ inside p n then fourier h (((Z/m-Z/n)/p : ℝ) : UnitAddCircle) else 0
  by_cases h₁ : inside p m <;> by_cases h₂ : inside p n
  · rw [if_pos h₁,if_pos h₂,if_pos ⟨h₁,h₂⟩,←fourier_neg,
      fourier_coe_apply,fourier_coe_apply,fourier_coe_apply,←Complex.exp_add]
    congr 1
    push_cast
    ring
  all_goals simp [h₁,h₂]

private theorem positive_gap_correlation {P V a b m n : ℕ} (hP : 1 ≤ P) (hV : 1 ≤ V)
    (ha : V ≤ a) (hb : b ≤ 2*V) (hm : m ∈ Ico a b) (hn : n ∈ Ico a b) (hmn : m < n)
    {Z : ℝ} (hZ : 0 < Z) {h : ℤ} (hh : h ≠ 0) (L U : ℕ) :
    let lower := Z/(16*(P : ℝ)^3*(V : ℝ)^2)
    let upper := Z*((b-a : ℕ) : ℝ)/(4*(P : ℝ)^3*(V : ℝ)^2)
    ‖∑ p ∈ Ico P (2*P), maskedReciprocalProduct Z h L U p m*
      (starRingEnd ℂ) (maskedReciprocalProduct Z h L U p n)‖ ≤
      (64*P*Real.sqrt upper+12/Real.sqrt lower)*Real.sqrt |(h : ℝ)| := by
  intro lower upper
  obtain ⟨ham,hmb⟩ := mem_Ico.mp hm
  obtain ⟨han,hnb⟩ := mem_Ico.mp hn
  have hp₀ : (0 : ℝ) < P := by exact_mod_cast hP
  have hv₀ : (0 : ℝ) < V := by exact_mod_cast hV
  have hm₁ := hV.trans (ha.trans ham)
  have hn₁ := hV.trans (ha.trans han)
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast hm₁
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn₁
  have gap : (1 : ℝ) ≤ (n : ℝ)-m := by
    have hh : (m : ℝ)+1 ≤ n := by exact_mod_cast (by omega : m+1 ≤ n)
    linarith only [hh]
  have span : (n : ℝ)-m ≤ ((b-a : ℕ) : ℝ) := by
    rw [Nat.cast_sub (ham.trans hmb.le)]
    have h₁ : (a : ℝ) ≤ m := by exact_mod_cast ham
    have h₂ : (n : ℝ) ≤ b := by exact_mod_cast hnb.le
    linarith only [h₁,h₂]
  have lo : (V : ℝ)^2 ≤ (m : ℝ)*n := by
    rw [sq]; exact_mod_cast Nat.mul_le_mul (ha.trans ham) (ha.trans han)
  have hi : (m : ℝ)*n ≤ 4*(V : ℝ)^2 := by
    have ht := Nat.mul_le_mul (hmb.le.trans hb) (hnb.le.trans hb)
    exact (by exact_mod_cast ht : (m : ℝ)*n ≤ (2*V)*(2*(V : ℝ))).trans_eq (by ring)
  let W := (Z/m-Z/n)
  have hW : W=Z*((n : ℝ)-m)/((m : ℝ)*n) := by dsimp [W]; field_simp
  have hw : 0 < W := by rw [hW]; exact div_pos (mul_pos hZ (by linarith only [gap])) (mul_pos hm₀ hn₀)
  let cur := 2*W/(2*(P : ℝ))^3
  have hden : 0 < 4*(P : ℝ)^3*((m : ℝ)*n) := by positivity
  have he : cur=Z*((n : ℝ)-m)/(4*(P : ℝ)^3*((m : ℝ)*n)) := by
    dsimp only [cur]; rw [hW]; ring
  have lower_le : lower ≤ cur := by
    rw [he]
    apply (div_le_div_of_nonneg_left hZ.le hden ?_).trans
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right hZ.le gap) hden.le)
    linarith only [mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 4*(P : ℝ)^3)]
  have le_upper : cur ≤ upper := by
    rw [he]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left span hZ.le) hden.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left lo (by positivity : 0 ≤ 4*(P : ℝ)^3)))
  have hl : 0 < lower := by dsimp [lower]; positivity
  have hu : 0 ≤ upper := hl.le.trans (lower_le.trans le_upper)
  let A := max P (max (L/m+1) (L/n+1))
  let B := min (2*P) (min (U/m+1) (U/n+1))
  rw [correlation_exact hm₁ hn₁]
  by_cases hab : A < B
  · have ht := integer_reciprocal_fourier_block hP (le_max_left ..) hab (min_le_left ..) hw hh
    apply ht.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt le_upper) (by positivity))
      (div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hl) (Real.sqrt_le_sqrt lower_le))
  · change ‖∑ p ∈ Ico A B, _‖ ≤ _
    rw [Ico_eq_empty (by omega),sum_empty,norm_zero]
    positivity

/-- On each short factor interval, all off-diagonal correlations save
through reciprocal curvature. The bound retains both coefficient energies
and arbitrary sharp endpoints on the product. -/
theorem short_interval_reciprocal_bilinear {P V a b : ℕ} (hP : 1 ≤ P) (hV : 1 ≤ V)
    (ha : V ≤ a) (hb : b ≤ 2*V) {Z : ℝ} (hZ : 0 < Z) {h : ℤ} (hh : h ≠ 0)
    (L U : ℕ) (α β : ℕ → ℂ) :
    let lower := Z/(16*(P : ℝ)^3*(V : ℝ)^2)
    let upper := Z*((b-a : ℕ) : ℝ)/(4*(P : ℝ)^3*(V : ℝ)^2)
    let E := (64*P*Real.sqrt upper+12/Real.sqrt lower)*Real.sqrt |(h : ℝ)|
    ‖∑ p ∈ Ico P (2*P), α p*∑ m ∈ Ico a b, β m*maskedReciprocalProduct Z h L U p m‖^2 ≤
      (∑ p ∈ Ico P (2*P), ‖α p‖^2)*(∑ m ∈ Ico a b, ‖β m‖^2)*(P+((b-a : ℕ) : ℝ)*E) := by
  intro lower upper E
  let D := Ico P (2*P)
  let J := Ico a b
  let z := maskedReciprocalProduct Z h L U
  let corr (m n : ℕ) := ∑ p ∈ D, z p m*(starRingEnd ℂ) (z p n)
  have nonneg : 0 ≤ E := by dsimp [E]; positivity
  let K (m n : ℕ) := E+(if m=n then (P : ℝ) else 0)
  have diag (m : ℕ) : ‖corr m m‖ ≤ P := by
    have bound (p : ℕ) : ‖z p m‖ ≤ 1 := by
      dsimp [z,maskedReciprocalProduct]
      split
      · exact (DeletionMixedRefinement.norm_fourier_real _ _).le
      · simp
    apply (norm_sum_le _ _).trans
    calc _ ≤ ∑ _p ∈ D, (1 : ℝ) := by
              apply sum_le_sum
              intro p _
              rw [norm_mul,RCLike.norm_conj]
              exact (mul_le_mul (bound p) (bound p) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
         _ = _ := by dsimp [D]; simp only [sum_const,Nat.card_Ico,nsmul_eq_mul,mul_one]; exact_mod_cast (by omega : 2*P-P=P)
  have symm (m n : ℕ) : ‖corr m n‖=‖corr n m‖ := by
    have id : (starRingEnd ℂ) (corr m n) = corr n m := by
      dsimp only [corr]
      rw [map_sum]
      apply sum_congr rfl
      intro p _
      rw [map_mul,RCLike.conj_conj,mul_comm]
    rw [←id,RCLike.norm_conj]
  have major (m : ℕ) (hm : m ∈ J) (n : ℕ) (hn : n ∈ J) : ‖corr m n‖ ≤ K m n := by
    rcases lt_trichotomy m n with hmn | rfl | hnm
    · simpa only [K,if_neg hmn.ne,add_zero] using
        positive_gap_correlation hP hV ha hb hm hn hmn hZ hh L U
    · exact (diag m).trans (by dsimp [K]; rw [if_pos rfl]; exact le_add_of_nonneg_left nonneg)
    · rw [symm]
      simpa only [K,if_neg hnm.ne',add_zero] using
        positive_gap_correlation hP hV ha hb hn hm hnm hZ hh L U
  have schur := RiemannGaussian.finset_symmetric_schur_quadratic_le J (fun m => ‖β m‖) K
    ((P : ℝ)+((b-a : ℕ) : ℝ)*E) (fun m n => by dsimp [K]; split <;> positivity)
    (fun m n => by
      rcases eq_or_ne m n with rfl | hmn
      · rfl
      · simp only [K,if_neg hmn,if_neg hmn.symm])
    (fun m hm => by
      simp only [K,sum_add_distrib,sum_const,nsmul_eq_mul,sum_ite_eq,if_pos hm]
      rw [show J.card = b-a from Nat.card_Ico a b,add_comm])
  have total := Sieve.sum_normSq_inner_le D J β z
  have hbnd : (∑ p ∈ D, ‖∑ m ∈ J, β m*z p m‖^2) ≤
      ((P : ℝ)+((b-a : ℕ) : ℝ)*E)*(∑ m ∈ J, ‖β m‖^2) := by
    apply total.trans (le_trans _ schur)
    apply sum_le_sum
    intro m hm
    apply sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (major m hm n hn) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (Sieve.norm_bilinear_sq_le D α (fun p => ∑ m ∈ J, β m*z p m)).trans
    ((mul_le_mul_of_nonneg_left hbnd (sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (by ring))

#print axioms short_interval_reciprocal_bilinear
end GaloisForLFunctions.PrimeExponentialSums
