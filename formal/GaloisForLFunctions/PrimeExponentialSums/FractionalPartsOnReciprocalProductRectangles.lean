import GaloisForLFunctions.PrimeExponentialSums.ReciprocalProductsOnShortFactorIntervals
import GaloisForLFunctions.RHTower.Sieve.KubalalikaDyadic

/-!
# Centered fractional parts on reciprocal product rectangles

Short intervals of the shorter factor limit the gap in the reciprocal
correlations. Their coefficient energies pay for the diagonal. The same
harmonic estimate applies to the absolute coefficient majorant, so the
sawtooth can be restored with a common smoothing width.
-/

noncomputable section
open Finset RHTower
open GaloisForLFunctions.HTGeometry.SmoothedSawtooth
namespace GaloisForLFunctions.PrimeExponentialSums

private theorem short_correlation_cost {P V H j : ℕ} (hH : 1 ≤ H) (hV : H ≤ V)
    (hP : H^4 ≤ P) (hj : j ≤ H) {Z : ℝ} (hZ : 0 < Z)
    (hzlo : ((P : ℝ)*V)^2 ≤ H*Z) (hzhi : Z ≤ H*((P : ℝ)*V)^2) :
    let u := Z/(16*(P : ℝ)^3*(V : ℝ)^2)
    let w := Z*(j : ℝ)/(4*(P : ℝ)^3*(V : ℝ)^2)
    (j : ℝ)*(64*P*Real.sqrt w+12/Real.sqrt u) ≤ 112*P := by
  intro u w
  have hr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hv : (0 : ℝ) < V := by exact_mod_cast hH.trans hV
  have hp : (0 : ℝ) < P := by exact_mod_cast (lt_of_lt_of_le (pow_pos hH 4) hP)
  have hh₀ := zero_lt_one.trans_le hr
  have hj' : (j : ℝ) ≤ H := by exact_mod_cast hj
  have hu : 0 < u := by dsimp [u]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have normU : u*(16*(P : ℝ)^3*(V : ℝ)^2)=Z := by dsimp [u]; field_simp
  have normW : w*(4*(P : ℝ)^3*(V : ℝ)^2)=Z*j := by dsimp [w]; field_simp
  have hsP := Real.sq_sqrt hp.le
  have hroot := Real.sqrt_pos.mpr hp
  have upper : (P : ℝ)*Real.sqrt w ≤ (H : ℝ)*Real.sqrt P := by
    have hh := mul_le_mul hzhi hj' (Nat.cast_nonneg j) (by positivity)
    have hsq : ((P : ℝ)*Real.sqrt w)^2*(4*(P : ℝ)*(V : ℝ)^2) ≤
        ((H : ℝ)*Real.sqrt P)^2*(4*(P : ℝ)*(V : ℝ)^2) := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hw,hsP]
      linarith only [normW,hh,mul_nonneg (Nat.cast_nonneg H) (mul_nonneg (sq_nonneg ((P : ℝ)*V)) (Nat.cast_nonneg H))]
    have hs := le_of_mul_le_mul_right hsq (by positivity : 0 < 4*(P : ℝ)*(V : ℝ)^2)
    nlinarith only [hs,mul_nonneg (Nat.cast_nonneg H) hroot.le,mul_nonneg hp.le (Real.sqrt_nonneg w)]
  have lower : 1/Real.sqrt u ≤ 4*(H : ℝ)*Real.sqrt P := by
    have hproof := mul_le_mul_of_nonneg_left hzlo (Nat.cast_nonneg (α := ℝ) H)
    have hones := le_mul_of_one_le_left (sq_nonneg ((P : ℝ)*V)) hr
    have hsq : 1*((P : ℝ)*V)^2 ≤ (4*(H : ℝ)*Real.sqrt P*Real.sqrt u)^2*((P : ℝ)*V)^2 := by
      have hid : (4*(H : ℝ)*Real.sqrt P*Real.sqrt u)^2*((P : ℝ)*V)^2=(H : ℝ)^2*Z := by
        rw [mul_pow,Real.sq_sqrt hu.le,mul_pow,hsP,←normU]; ring
      rw [hid,one_mul]
      linarith only [hproof,hones]
    have hs := le_of_mul_le_mul_right hsq (sq_pos_of_pos (mul_pos hp hv))
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hu)).mpr
    nlinarith only [hs,show 0 ≤ 4*(H : ℝ)*Real.sqrt P*Real.sqrt u by positivity]
  have htop : (H : ℝ)^2 ≤ Real.sqrt P := (Real.le_sqrt (sq_nonneg _) hp.le).mpr (by
    have h := (by exact_mod_cast hP : (H : ℝ)^4 ≤ P)
    nlinarith only [h])
  have hcost : 64*P*Real.sqrt w+12/Real.sqrt u ≤ 112*(H : ℝ)*Real.sqrt P := by
    simp only [div_eq_mul_inv,one_mul] at lower ⊢
    linarith only [upper,lower]
  have ht := mul_le_mul hj' hcost (by positivity) (Nat.cast_nonneg H)
  have hs := mul_le_mul_of_nonneg_right htop hroot.le
  rw [←sq,hsP] at hs
  linarith only [ht,hs]

private theorem interval_energy {a b : ℕ} (f : ℕ → ℂ) {A : ℝ}
    (h : ∀ n ∈ Ico a b, ‖f n‖ ≤ A) :
    (∑ n ∈ Ico a b, ‖f n‖^2) ≤ ((b-a : ℕ) : ℝ)*A^2 := by
  calc _ ≤ ∑ _n ∈ Ico a b, A^2 := sum_le_sum fun n hn => pow_le_pow_left₀ (norm_nonneg _) (h n hn) 2
       _ = _ := by rw [sum_const,Nat.card_Ico,nsmul_eq_mul]

private theorem short_harmonic {P V H a b : ℕ} (hH : 1 ≤ H) (hV : H ≤ V) (hP : H^4 ≤ P)
    (ha : V ≤ a) (hb : b ≤ 2*V) (hlen : b-a ≤ H) {Z : ℝ} (hZ : 0 < Z)
    (hzlo : ((P : ℝ)*V)^2 ≤ H*Z) (hzhi : Z ≤ H*((P : ℝ)*V)^2)
    {h : ℤ} (hh : h ≠ 0) (L U : ℕ) (α β : ℕ → ℂ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ p ∈ Ico P (2*P), ‖α p‖ ≤ A) (hβ : ∀ m ∈ Ico a b, ‖β m‖ ≤ B) :
    ‖∑ p ∈ Ico P (2*P), α p*∑ m ∈ Ico a b, β m*maskedReciprocalProduct Z h L U p m‖ ≤
      11*A*B*P*Real.sqrt H*Real.sqrt |(h : ℝ)| := by
  let j := b-a
  let u := Z/(16*(P : ℝ)^3*(V : ℝ)^2)
  let w := Z*(j : ℝ)/(4*(P : ℝ)^3*(V : ℝ)^2)
  let C := 64*P*Real.sqrt w+12/Real.sqrt u
  have hc : (j : ℝ)*C ≤ 112*P := short_correlation_cost hH hV hP hlen hZ hzlo hzhi
  have hfreq : (1 : ℝ) ≤ |(h : ℝ)| := by
    have hpos : 0 < |h| := abs_pos.mpr hh
    exact_mod_cast (show (1 : ℤ) ≤ |h| by omega)
  let r := Real.sqrt |(h : ℝ)|
  have hr : 1 ≤ r := Real.one_le_sqrt.mpr hfreq
  have hr₀ := zero_le_one.trans hr
  have hp := (show 1 ≤ H^4 from Nat.one_le_pow 4 H hH).trans hP
  have hrow : (P : ℝ)+j*(C*r) ≤ 113*P*r^2 := by
    have h₁ := le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) P) hr
    have h₂ := mul_le_mul_of_nonneg_right hc hr₀
    have h₃ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hr₀ hr) (Nat.cast_nonneg (α := ℝ) P)
    linarith only [h₁,h₂,h₃]
  have hα' := interval_energy α hα
  rw [show 2*P-P=P by omega] at hα'
  have hβ' := (interval_energy β hβ).trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hlen : ((b-a : ℕ) : ℝ) ≤ H) (sq_nonneg _))
  have hprod := mul_le_mul hα' hβ' (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  have hen := short_interval_reciprocal_bilinear hp (hH.trans hV) ha hb hZ hh L U α β
  change _ ≤ _*((P : ℝ)+j*(C*r)) at hen
  have htop := hen.trans (mul_le_mul hprod hrow (by dsimp [C,r,u,w]; positivity) (by positivity))
  have hs : ((P : ℝ)*A^2*(H*B^2))*(113*P*r^2) ≤ (11*A*B*P*Real.sqrt H*r)^2 := by
    have ht : (11*A*B*P*Real.sqrt H*r)^2 = 121*((P : ℝ)*A^2*(H*B^2))*(P*r^2) := by
      simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg H)]; ring
    rw [ht]
    nlinarith only [show 0 ≤ ((P : ℝ)*A^2*(H*B^2))*(P*r^2) by positivity]
  have hh' := htop.trans hs
  nlinarith only [hh',show 0 ≤ 11*A*B*P*Real.sqrt H*r by positivity,norm_nonneg
    (∑ p ∈ Ico P (2*P), α p*∑ m ∈ Ico a b, β m*maskedReciprocalProduct Z h L U p m)]

/-- Full dyadic factor rectangle with arbitrary coefficients and both
product endpoints retained at every nonzero Fourier harmonic. -/
theorem reciprocal_rectangle_harmonic {P V H : ℕ} (hH : 1 ≤ H) (hV : H ≤ V) (hP : H^4 ≤ P)
    {Z : ℝ} (hZ : 0 < Z) (hzlo : ((P : ℝ)*V)^2 ≤ H*Z) (hzhi : Z ≤ H*((P : ℝ)*V)^2)
    {h : ℤ} (hh : h ≠ 0) (L U : ℕ) (α β : ℕ → ℂ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ p ∈ Ico P (2*P), ‖α p‖ ≤ A) (hβ : ∀ m ∈ Ico V (2*V), ‖β m‖ ≤ B) :
    ‖∑ p ∈ Ico P (2*P), α p*∑ m ∈ Ico V (2*V), β m*maskedReciprocalProduct Z h L U p m‖ ≤
      (22*A*B*P*V/Real.sqrt H)*Real.sqrt |(h : ℝ)| := by
  let N := V/H+1
  let c (j : ℕ) := min (2*V) (V+j*H)
  have hc : Monotone c := fun _ _ hj => min_le_min_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right H hj) V)
  have h₀ : c 0 = V := by simp [c]; omega
  have hlast : c N=2*V := by
    have ht := Nat.lt_mul_div_succ V hH
    dsimp [c,N]; apply min_eq_left
    rw [Nat.mul_comm (V/H+1)]; omega
  have flip (s : Finset ℕ) : (∑ p ∈ Ico P (2*P), α p*∑ m ∈ s, β m*maskedReciprocalProduct Z h L U p m) =
      ∑ m ∈ s, ∑ p ∈ Ico P (2*P), α p*(β m*maskedReciprocalProduct Z h L U p m) := by
    simp_rw [mul_sum]; exact sum_comm
  let f (m : ℕ) := ∑ p ∈ Ico P (2*P), α p*(β m*maskedReciprocalProduct Z h L U p m)
  have hpart : (∑ m ∈ Ico V (2*V), f m) = ∑ j ∈ range N, ∑ m ∈ Ico (c j) (c (j+1)), f m := by
    simpa only [h₀,hlast] using Sieve.sum_Ico_monotone_partition f c hc N
  let E := 11*A*B*P*Real.sqrt H*Real.sqrt |(h : ℝ)|
  have hblock (j : ℕ) : ‖∑ m ∈ Ico (c j) (c (j+1)), f m‖ ≤ E := by
    have hVj : V ≤ c j := le_min (by omega) (Nat.le_add_right ..)
    have hje : c (j+1) ≤ 2*V := min_le_left ..
    have hs : c (j+1)-c j ≤ H := by dsimp [c]; rw [Nat.add_mul,Nat.one_mul]; omega
    have hβj (m : ℕ) (hm : m ∈ Ico (c j) (c (j+1))) := hβ m
      (mem_Ico.mpr ⟨hVj.trans (mem_Ico.mp hm).1,(mem_Ico.mp hm).2.trans_le hje⟩)
    have ht := short_harmonic hH hV hP hVj hje hs hZ hzlo hzhi hh L U α β hA hB hα hβj
    rw [flip] at ht
    exact ht
  rw [flip]
  change ‖∑ m ∈ Ico V (2*V), f m‖ ≤ _
  rw [hpart]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun j _ => hblock j)).trans
  rw [sum_const,card_range,nsmul_eq_mul]
  have hcost : (N : ℝ)*H ≤ 2*V := by
    have hn : N*H ≤ 2*V := by dsimp [N]; rw [Nat.add_mul,Nat.one_mul]; have := Nat.div_mul_le_self V H; omega
    exact_mod_cast hn
  have hroot : 0 < Real.sqrt H := Real.sqrt_pos.mpr (by exact_mod_cast hH)
  have hN : (N : ℝ)*Real.sqrt H ≤ 2*V/Real.sqrt H := by
    apply (le_div_iff₀ hroot).mpr
    rw [mul_assoc,←sq,Real.sq_sqrt (Nat.cast_nonneg H)]
    exact hcost
  have he := mul_le_mul_of_nonneg_right hN (by positivity : 0 ≤ 11*A*B*P*Real.sqrt |(h : ℝ)|)
  dsimp only [E]
  simp only [div_eq_mul_inv] at he ⊢
  linarith only [he]

/-- Centered reciprocal fractional parts cancel on the full factor
rectangle, uniformly in both product endpoints and all coefficient signs. -/
theorem centered_fractional_reciprocal_product_rectangle :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {P V H : ℕ}, 1 ≤ H → H ≤ V → H^4 ≤ P →
      ∀ {Z : ℝ}, 0 < Z → ((P : ℝ)*V)^2 ≤ H*Z → Z ≤ H*((P : ℝ)*V)^2 →
      ∀ (L U : ℕ) (α β : ℕ → ℂ) {A B : ℝ}, 0 ≤ A → 0 ≤ B →
        (∀ p ∈ Ico P (2*P), ‖α p‖ ≤ A) → (∀ m ∈ Ico V (2*V), ‖β m‖ ≤ B) →
      ‖∑ q ∈ (Ico P (2*P) ×ˢ Ico V (2*V)) with L < q.1*q.2 ∧ q.1*q.2 ≤ U,
        (α q.1*β q.2)*(saw (Z/q.2/q.1) : ℂ)‖ ≤ K*(A*B*P*V)/Real.sqrt (Real.sqrt H) := by
  obtain ⟨K,hK,hsaw⟩ := sawtooth_of_sqrt_harmonics
  refine ⟨23*K,by positivity,?_⟩
  intro P V H hH hV hP Z hZ hzlo hzhi L U α β A B hA hB hα hβ
  let D := Ico P (2*P)
  let J := Ico V (2*V)
  let S := (D ×ˢ J).filter (fun q => L < q.1*q.2 ∧ q.1*q.2 ≤ U)
  let y (q : ℕ×ℕ) := Z/q.2/q.1
  let coeff (q : ℕ×ℕ) := α q.1*β q.2
  let major (q : ℕ×ℕ) := ‖α q.1‖*‖β q.2‖
  let weight := A*B*P*V
  let root := Real.sqrt (Real.sqrt H)
  have hroot : 0 < root := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hH))
  have hroot_sq : root^2=Real.sqrt H := Real.sq_sqrt (Real.sqrt_nonneg _)
  let M := 22*weight/Real.sqrt H
  have hweight : 0 ≤ weight := by dsimp [weight]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have repr (c d : ℕ → ℂ) (h : ℤ) :
      (∑ q ∈ S, (c q.1*d q.2)*fourier h (y q : UnitAddCircle)) =
        ∑ p ∈ D, c p*∑ m ∈ J, d m*maskedReciprocalProduct Z h L U p m := by
    dsimp only [S]
    rw [sum_filter,sum_product]
    apply sum_congr rfl
    intro p _
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    by_cases hcut : L<p*m ∧ p*m≤U <;> simp [maskedReciprocalProduct,y,hcut,mul_assoc]
  have freq (h : ℤ) (hh : h ≠ 0) :
      ‖∑ q ∈ S, coeff q*fourier h (y q : UnitAddCircle)‖ ≤ M*Real.sqrt |(h : ℝ)| ∧
      ‖∑ q ∈ S, (major q : ℂ)*fourier h (y q : UnitAddCircle)‖ ≤ M*Real.sqrt |(h : ℝ)| := by
    constructor
    · dsimp only [coeff]
      rw [repr]
      exact (reciprocal_rectangle_harmonic hH hV hP hZ hzlo hzhi hh L U α β hA hB hα hβ).trans_eq
        (by dsimp [M,weight]; ring)
    · dsimp only [major]; simp only [Complex.ofReal_mul]
      rw [repr (fun p => (‖α p‖ : ℂ)) (fun m => (‖β m‖ : ℂ))]
      have hc (p : ℕ) (hp : p ∈ D) : ‖(‖α p‖ : ℂ)‖ ≤ A := by simpa using hα p hp
      have hd (m : ℕ) (hm : m ∈ J) : ‖(‖β m‖ : ℂ)‖ ≤ B := by simpa using hβ m hm
      exact (reciprocal_rectangle_harmonic hH hV hP hZ hzlo hzhi hh L U _ _ hA hB hc hd).trans_eq
        (by dsimp [M,weight]; ring)
  have hcard : (S.card : ℝ) ≤ (P : ℝ)*V := by
    have hh := card_le_card (filter_subset (fun q : ℕ×ℕ => L<q.1*q.2 ∧ q.1*q.2≤U) (D ×ˢ J))
    rw [card_product,show D.card=P from (Nat.card_Ico ..).trans (by omega),
      show J.card=V from (Nat.card_Ico ..).trans (by omega)] at hh
    exact_mod_cast hh
  have mass : (∑ q ∈ S, major q) ≤ weight := by
    calc _ ≤ ∑ _q ∈ S, A*B := by
              apply sum_le_sum
              intro q hq
              obtain ⟨hp,hm⟩ := mem_product.mp (mem_filter.mp hq).1
              exact mul_le_mul (hα _ hp) (hβ _ hm) (norm_nonneg _) hA
         _ ≤ _ := by
              rw [sum_const,nsmul_eq_mul]
              exact (mul_le_mul_of_nonneg_right hcard (mul_nonneg hA hB)).trans_eq (by dsimp [weight]; ring)
  have h := hsaw S y coeff major (one_div_pos.mpr hroot) hM
    (fun q => by simp only [coeff,major,norm_mul,le_refl]) freq
  apply h.trans
  have he : M/(1/root)=22*weight/root := by
    dsimp only [M]
    rw [←hroot_sq]; field_simp
  rw [he]
  apply (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left mass (one_div_nonneg.mpr hroot.le)) le_rfl) hK).trans_eq
  ring

#print axioms reciprocal_rectangle_harmonic
#print axioms centered_fractional_reciprocal_product_rectangle
end GaloisForLFunctions.PrimeExponentialSums
