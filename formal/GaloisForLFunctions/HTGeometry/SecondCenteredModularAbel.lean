import GaloisForLFunctions.HTGeometry.CenteredModularAbel

/-!
# Second centering of modular Abel responses

The quadratic residue primitive has a nonzero period mean. A periodic cubic
primitive removes that mean and yields an exact second Abel identity. The
half-order clock has a decreasing first difference with cubic birth decay,
so the remaining error is bounded by the reciprocal of the modulus.
-/

noncomputable section
open Finset
namespace HTGeometry

/-- The positive magnitude of the period mean of the first centered modular primitive. -/
def centeredModularMeanMagnitude (d : ℕ) : ℝ := ((d:ℝ)^(2 : ℕ)-1)/(12*d)

/-- Periodic cubic primitive of the mean-corrected shifted quadratic primitive. -/
def centeredModularSecondPrimitive (d N : ℕ) : ℝ :=
  (N%d:ℕ)*((d:ℝ)-(N%d:ℕ))*((d:ℝ)-3-2*(N%d:ℕ))/(12*d)

@[simp] theorem centeredModularSecondPrimitive_zero (d : ℕ) :
    centeredModularSecondPrimitive d 0=0 := by simp [centeredModularSecondPrimitive]

/-- The second primitive differentiates to the shifted first primitive with its mean removed, including every period wrap. -/
theorem centeredModularSecondPrimitive_succ {d : ℕ} (hd : 0<d) (N : ℕ) :
    centeredModularSecondPrimitive d (N+1)-centeredModularSecondPrimitive d N =
      centeredModularPrimitive d (N+1)+centeredModularMeanMagnitude d := by
  have hres := Nat.mod_lt N hd
  have hmod : (N+1)%d=(N%d+1)%d := by simp [Nat.add_mod]
  by_cases h : N%d+1<d
  · have he : (N+1)%d=N%d+1 := by rw [hmod,Nat.mod_eq_of_lt h]
    unfold centeredModularSecondPrimitive centeredModularPrimitive centeredModularMeanMagnitude
    rw [he]
    push_cast
    field_simp
    ring
  · have he : (N+1)%d=0 := by rw [hmod,show N%d+1=d by omega,Nat.mod_self]
    unfold centeredModularSecondPrimitive centeredModularPrimitive centeredModularMeanMagnitude
    rw [he]
    push_cast
    have hr' : ((N%d:ℕ):ℝ)=(d:ℝ)-1 := by
      have hx : ((N%d:ℕ):ℝ)+1=d := by exact_mod_cast (show N%d+1=d by omega)
      linarith only [hx]
    rw [hr']
    field_simp
    ring

/-- The periodic cubic primitive has a uniform quadratic-modulus bound. -/
theorem abs_centeredModularSecondPrimitive_le (d N : ℕ) :
    |centeredModularSecondPrimitive d N| ≤ (d:ℝ)^(2 : ℕ)/12 := by
  by_cases hd : d=0
  · simp [hd,centeredModularSecondPrimitive]
  have hd0 : (0:ℝ)<d := by positivity
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  let r : ℝ := (N%d:ℕ)
  have hr0 : 0≤r := Nat.cast_nonneg _
  have hrd : r≤d := by
    dsimp [r]
    exact_mod_cast (Nat.mod_lt N (show 0<d by omega)).le
  have hp0 : 0≤r*((d:ℝ)-r) := mul_nonneg hr0 (sub_nonneg.mpr hrd)
  have hp : r*((d:ℝ)-r)≤(d:ℝ)^(2 : ℕ)/4 := by nlinarith [sq_nonneg (r-(d:ℝ)/2)]
  have hb : |(d:ℝ)-3-2*r|≤4*d := by
    apply abs_le.mpr
    constructor <;> linarith only [hr0,hrd,hd1]
  have hmul := mul_le_mul_of_nonneg_left hb hp0
  have hmul' := mul_le_mul_of_nonneg_right hp (show (0:ℝ)≤4*d by positivity)
  change |r*((d:ℝ)-r)*((d:ℝ)-3-2*r)/(12*d)|≤_
  rw [abs_div,abs_mul,abs_of_nonneg hp0,abs_of_pos (by positivity : (0:ℝ)<12*d),div_le_iff₀ (by positivity)]
  nlinarith only [hmul,hmul']

private theorem second_primitive_abel {d : ℕ} (hd : 0<d) (N : ℕ) (g : ℕ → ℝ) :
    (∑ k ∈ range N,(centeredModularPrimitive d (k+1)+centeredModularMeanMagnitude d)*g k) =
      (∑ k ∈ range N,centeredModularSecondPrimitive d (k+1)*(g k-g (k+1)))+
        centeredModularSecondPrimitive d N*g N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,sum_range_succ,ih]
    have h := congrArg (fun x : ℝ => x*g N) (centeredModularSecondPrimitive_succ hd N)
    nlinarith only [h]

/-- Second Abel summation keeps the exact primitive mean and moving residue boundary. -/
theorem centeredModularRamp_second_abel (d N : ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ range N,centeredModularRamp d k*w k)+centeredModularMeanMagnitude d*w 0-
      (centeredModularMeanMagnitude d+centeredModularPrimitive d N)*w N =
      (∑ k ∈ range N,centeredModularSecondPrimitive d (k+1)*
        ((w k-w (k+1))-(w (k+1)-w (k+2))))+
      centeredModularSecondPrimitive d N*(w N-w (N+1)) := by
  by_cases hd : d=0
  · simp [hd,centeredModularMeanMagnitude,centeredModularRamp,centeredModularPrimitive,centeredModularSecondPrimitive]
  have h := second_primitive_abel (by omega : 0<d) N (fun k => w k-w (k+1))
  simp only [add_mul,sum_add_distrib,← mul_sum] at h
  have htel : (∑ k ∈ range N,(w k-w (k+1)))=w 0-w N := by
    simpa only [neg_sub,← sum_neg_distrib] using congrArg Neg.neg (sum_range_sub w N)
  rw [htel] at h
  rw [sum_centeredModularRamp_mul_eq]
  simp only [Nat.add_assoc] at h
  linarith only [h]

/-- A decreasing nonnegative first weight difference charges the entire second-centered error only to its initial value. -/
theorem abs_centeredModularRamp_second_abel_le (d N : ℕ) (w : ℕ → ℝ)
    (hg : ∀ k,0≤w k-w (k+1)) (hmono : Antitone (fun k => w k-w (k+1))) :
    |(∑ k ∈ range N,centeredModularRamp d k*w k)+centeredModularMeanMagnitude d*w 0-
      (centeredModularMeanMagnitude d+centeredModularPrimitive d N)*w N| ≤
        (d:ℝ)^(2 : ℕ)/12*(w 0-w 1) := by
  rw [centeredModularRamp_second_abel]
  let g := fun k => w k-w (k+1)
  have hd (k : ℕ) : 0≤g k-g (k+1) := sub_nonneg.mpr (hmono (by omega))
  have htel : (∑ k ∈ range N,(g k-g (k+1)))+g N=g 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ]; linarith
  have hs : |∑ k ∈ range N,centeredModularSecondPrimitive d (k+1)*(g k-g (k+1))| ≤
      (d:ℝ)^(2 : ℕ)/12*(∑ k ∈ range N,(g k-g (k+1))) := by
    calc
      _ ≤ ∑ k ∈ range N,|centeredModularSecondPrimitive d (k+1)*(g k-g (k+1))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range N,((d:ℝ)^(2 : ℕ)/12)*(g k-g (k+1)) := by
        apply sum_le_sum
        intro k hk
        rw [abs_mul,abs_of_nonneg (hd k)]
        exact mul_le_mul_of_nonneg_right (abs_centeredModularSecondPrimitive_le d (k+1)) (hd k)
      _ = _ := by rw [mul_sum]
  have ht : |centeredModularSecondPrimitive d N*g N| ≤ (d:ℝ)^(2 : ℕ)/12*g N := by
    rw [abs_mul,abs_of_nonneg (hg N)]
    exact mul_le_mul_of_nonneg_right (abs_centeredModularSecondPrimitive_le d N) (hg N)
  change |(∑ k ∈ range N,centeredModularSecondPrimitive d (k+1)*(g k-g (k+1)))+
    centeredModularSecondPrimitive d N*g N| ≤ (d:ℝ)^(2 : ℕ)/12*g 0
  have htri := abs_add_le (∑ k ∈ range N,centeredModularSecondPrimitive d (k+1)*(g k-g (k+1)))
    (centeredModularSecondPrimitive d N*g N)
  have he := congrArg (fun x : ℝ => (d:ℝ)^(2 : ℕ)/12*x) htel
  nlinarith only [hs,ht,htri,he]

private theorem sqrt_step_reciprocal (n : ℕ) :
    Real.sqrt (n+1:ℕ)-Real.sqrt n=1/(Real.sqrt n+Real.sqrt (n+1:ℕ)) := by
  have hn := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hn1 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
  rw [eq_div_iff (by positivity)]
  push_cast at hn1 ⊢
  nlinarith only [hn,hn1]

/-- Exact reciprocal formula for the first difference of the half-order clock. -/
theorem halfOrderAbelStep_gap_eq (B k : ℕ) :
    halfOrderAbelStep B k-halfOrderAbelStep B (k+1) =
      2/((Real.sqrt (B+k:ℕ)+Real.sqrt (B+k+1:ℕ))*
        (Real.sqrt (B+k+1:ℕ)+Real.sqrt (B+k+2:ℕ))*
        (Real.sqrt (B+k:ℕ)+Real.sqrt (B+k+2:ℕ))) := by
  change (Real.sqrt (B+k+1:ℕ)-Real.sqrt (B+k:ℕ))-
    (Real.sqrt (B+k+2:ℕ)-Real.sqrt (B+k+1:ℕ)) = _
  have hn := sqrt_step_reciprocal (B+k)
  have hn1 : Real.sqrt (B+k+2:ℕ)-Real.sqrt (B+k+1:ℕ) =
      1/(Real.sqrt (B+k+1:ℕ)+Real.sqrt (B+k+2:ℕ)) := sqrt_step_reciprocal (B+k+1)
  have ha := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (B+k))
  have hc := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (B+k+2))
  have hdiff : Real.sqrt (B+k+2:ℕ)-Real.sqrt (B+k:ℕ) =
      2/(Real.sqrt (B+k:ℕ)+Real.sqrt (B+k+2:ℕ)) := by
    rw [eq_div_iff (by positivity)]
    push_cast at ha hc ⊢
    nlinarith only [ha,hc]
  rw [hn,hn1]
  have he : 1/(Real.sqrt (B+k:ℕ)+Real.sqrt (B+k+1:ℕ))-
      1/(Real.sqrt (B+k+1:ℕ)+Real.sqrt (B+k+2:ℕ)) =
      (Real.sqrt (B+k+2:ℕ)-Real.sqrt (B+k:ℕ))/
        ((Real.sqrt (B+k:ℕ)+Real.sqrt (B+k+1:ℕ))*(Real.sqrt (B+k+1:ℕ)+Real.sqrt (B+k+2:ℕ))) := by
    field_simp
    ring
  rw [he,hdiff]
  field_simp

/-- The positive first difference of the half-order clock is itself decreasing. -/
theorem halfOrderAbelStep_gap_antitone (B : ℕ) :
    Antitone (fun k => halfOrderAbelStep B k-halfOrderAbelStep B (k+1)) := by
  intro i j hij
  dsimp only
  rw [halfOrderAbelStep_gap_eq,halfOrderAbelStep_gap_eq]
  have ha : Real.sqrt (B+i:ℕ) ≤ Real.sqrt (B+j:ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show B+i≤B+j by omega))
  have hb : Real.sqrt (B+i+1:ℕ) ≤ Real.sqrt (B+j+1:ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show B+i+1≤B+j+1 by omega))
  have hc : Real.sqrt (B+i+2:ℕ) ≤ Real.sqrt (B+j+2:ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show B+i+2≤B+j+2 by omega))
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul (mul_le_mul (add_le_add ha hb) (add_le_add hb hc) (by positivity) (by positivity))
    (add_le_add ha hc) (by positivity) (by positivity)

/-- At a square birth, the clock difference has cubic decay in the modulus. -/
theorem halfOrderAbelStep_square_gap_le {d : ℕ} (hd : 0<d) :
    halfOrderAbelStep (d*d) 0-halfOrderAbelStep (d*d) 1 ≤ 1/(4*(d:ℝ)^(3 : ℕ)) := by
  rw [halfOrderAbelStep_gap_eq]
  simp only [Nat.add_zero]
  have he : Real.sqrt (d*d:ℕ)=(d:ℝ) := by
    rw [Nat.cast_mul,Real.sqrt_mul_self (Nat.cast_nonneg d)]
  rw [he]
  have h1 : (d:ℝ)≤Real.sqrt (d*d+1:ℕ) := by
    rw [← he]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show d*d≤d*d+1 by omega))
  have h2 : (d:ℝ)≤Real.sqrt (d*d+2:ℕ) := by
    rw [← he]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show d*d≤d*d+2 by omega))
  have hden : (2*(d:ℝ))^(3 : ℕ) ≤
      ((d:ℝ)+Real.sqrt (d*d+1:ℕ))*(Real.sqrt (d*d+1:ℕ)+Real.sqrt (d*d+2:ℕ))*
      ((d:ℝ)+Real.sqrt (d*d+2:ℕ)) := by
    have h := mul_le_mul (mul_le_mul (by linarith only [h1] : 2*(d:ℝ)≤(d:ℝ)+Real.sqrt (d*d+1:ℕ))
      (by linarith only [h1,h2] : 2*(d:ℝ)≤Real.sqrt (d*d+1:ℕ)+Real.sqrt (d*d+2:ℕ))
      (by positivity) (by positivity))
      (by linarith only [h2] : 2*(d:ℝ)≤(d:ℝ)+Real.sqrt (d*d+2:ℕ)) (by positivity) (by positivity)
    nlinarith only [h]
  calc
    _ ≤ 2/(2*(d:ℝ))^(3 : ℕ) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = _ := by field_simp; ring

/-- The half-order centered modular response has an exact-mean approximation with reciprocal-modulus error. -/
theorem abs_centeredModularRamp_halfOrder_mean_error_le {d : ℕ} (hd : 0<d) (N : ℕ) :
    |(∑ k ∈ range N,centeredModularRamp d k*halfOrderAbelStep (d*d) k)+
      centeredModularMeanMagnitude d*halfOrderAbelStep (d*d) 0-
      (centeredModularMeanMagnitude d+centeredModularPrimitive d N)*halfOrderAbelStep (d*d) N| ≤
        1/(48*(d:ℝ)) := by
  have h := abs_centeredModularRamp_second_abel_le d N (halfOrderAbelStep (d*d))
    (fun k => sub_nonneg.mpr (halfOrderAbelStep_antitone (d*d) (show k≤k+1 by omega)))
    (halfOrderAbelStep_gap_antitone (d*d))
  have hgap := mul_le_mul_of_nonneg_left (halfOrderAbelStep_square_gap_le hd)
    (show (0:ℝ)≤(d:ℝ)^(2 : ℕ)/12 by positivity)
  have he : (d:ℝ)^(2 : ℕ)/12*(1/(4*(d:ℝ)^(3 : ℕ)))=1/(48*(d:ℝ)) := by field_simp; ring
  rw [he] at hgap
  exact h.trans hgap

/-- The first primitive has the exact negative mean used by the cubic correction. -/
theorem sum_centeredModularPrimitive_period (d : ℕ) :
    (∑ k ∈ range d,centeredModularPrimitive d (k+1)) = -(d:ℝ)*centeredModularMeanMagnitude d := by
  by_cases hd : d=0
  · simp [hd]
  have hsum : (∑ k ∈ range d,(centeredModularPrimitive d (k+1)+centeredModularMeanMagnitude d))=0 := by
    simp_rw [← centeredModularSecondPrimitive_succ (show 0<d by omega)]
    rw [sum_range_sub]
    simp [centeredModularSecondPrimitive]
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hsum
  linarith only [hsum]

/-- The reciprocal-modulus error survives the literal square birth and the entire moving terminal block. -/
theorem abs_centeredModularRamp_halfOrder_Ico_mean_error_le {d M : ℕ} (hd : 0<d) (hM : d*d≤M) :
    |(∑ k ∈ Ico (d*d) M,centeredModularRamp d k*halfOrderAbelStep 0 k)+
      centeredModularMeanMagnitude d*halfOrderAbelStep (d*d) 0-
      (centeredModularMeanMagnitude d+centeredModularPrimitive d M)*halfOrderAbelStep 0 M| ≤
        1/(48*(d:ℝ)) := by
  have h := abs_centeredModularRamp_halfOrder_mean_error_le hd (M-d*d)
  have he : d*d+(M-d*d)=M := Nat.add_sub_of_le hM
  have hP : centeredModularPrimitive d (M-d*d)=centeredModularPrimitive d M := by
    conv_rhs => rw [← he]
    simp [centeredModularPrimitive,Nat.add_mod]
  rw [hP] at h
  rw [sum_Ico_eq_sum_range]
  simpa only [centeredModularRamp_mul_add,halfOrderAbelStep,Nat.zero_add,he] using h
end HTGeometry
