import GaloisForLFunctions.SignedArithmeticCorrespondences.GluingIntegerGraphsAtTheirQuotientEndpoints
import GaloisForLFunctions.SignedArithmeticCorrespondences.TheRealPlaceAfterGluingSignedEndpoints

/-!
# Opposing sections for the joint integral graph height and Weil row

Put the lower graphs below a cut X and the upper endpoints at or beyond X+L.
Retaining the local orders with the flat-tail row leaves one integral of the
two glued sections. Its density is x^L(1−x), independently of both supports.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open Finset ArithmeticCastelnuovoSeveri HodgeTheoryOfAFixedPart MeasureTheory _root_.RHTower
open scoped Topology

/-- Jumps across the upper side of a cut with gap L. -/
def farJump (X L : ℕ) (b : ℕ → ℤ) (j : ℕ) : ℤ := if X+L ≤ j then b j else 0

/-- Add the actual mixed graph order minus the pole product to the signed
Weil rows. Each row is measured relative to its own constant diagonal term. -/
def jointGraphHeight (X N L : ℕ) (u b : ℕ → ℤ) : ℝ :=
  signedDivisorHeight 1 X N u (upperDivisor N (farJump X L b)) - poleProduct X N u (farJump X L b) +
    ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i:ℝ)*farJump X L b j*
      (tailPotential (Icc 1 j) i - (3/(4*(i:ℝ)) - Real.log (2*Real.pi)))

/-- The mixed Weil row itself, after its constant diagonal and the fractional
endpoint correction have been removed. Its prime-contact contribution remains. -/
def centeredWeilRow (X N L : ℕ) (u b : ℕ → ℤ) : ℝ :=
  (∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i:ℝ)*farJump X L b j*
    (tailPotential (Icc 1 j) i - (3/(4*(i:ℝ)) - Real.log (2*Real.pi)))) -
    fractionalBoundary X N u (farJump X L b)

theorem centeredWeilRow_eq (X N L : ℕ) (u b : ℕ → ℤ) :
    centeredWeilRow X N L u b = jointGraphHeight X N L u b -
      (signedDivisorHeight 1 X N u (upperDivisor N (farJump X L b)) -
        poleProduct X N u (farJump X L b) + fractionalBoundary X N u (farJump X L b)) := by
  unfold centeredWeilRow jointGraphHeight
  ring

/-- A lower graph gives the translated square of its geometric sum. -/
def lowerSection (X : ℕ) (u : ℕ → ℤ) (x : ℝ) : ℝ :=
  ∑ i ∈ Icc 1 X, (u i:ℝ)*x^(X-i)*(∑ a ∈ range i, x^a)^2

/-- The upper section records the signed jumps measured from the far cut. -/
def upperSection (X N L : ℕ) (b : ℕ → ℤ) (x : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 N, (farJump X L b j:ℝ)*x^(j-(X+L))

private theorem joint_row_sum (X N L : ℕ) (u b : ℕ → ℤ) :
    jointGraphHeight X N L u b =
      ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i:ℝ)*farJump X L b j*realEndpoint i (j-i) := by
  rw [jointGraphHeight,height_eq_quotient,poleProduct,sum_mul_sum]
  simp only [← sum_sub_distrib,← sum_add_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j _ => ?_
  by_cases hj : X+L ≤ j
  · have hiX := (mem_Icc.mp hi).2
    rw [realEndpoint,show i+(j-i)=j by omega]
    change (u i:ℝ)*farJump X L b j*chebyshev (j/i) - _ + _ = _
    ring
  · simp [farJump,hj]

/-- Exact common normalization of the vertical order, pole product and real
metric after both signed divisors are glued. This includes the cut L=0. -/
theorem jointGraphHeight_sections (X N L : ℕ) (u b : ℕ → ℤ) :
    2*jointGraphHeight X N L u b =
      ∫ x in (0:ℝ)..1, x^L*(1-x)*(lowerSection X u x*upperSection X N L b x) := by
  have h (x : ℝ) : x^L*(1-x)*(lowerSection X u x*upperSection X N L b x) =
      ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, ((u i:ℝ)*farJump X L b j)*
        (x^(j-i)*(1-x)*(∑ a ∈ range i, x^a)^2) := by
    rw [lowerSection,upperSection,sum_mul_sum]
    simp only [mul_sum]
    refine sum_congr rfl fun i hi => sum_congr rfl fun j _ => ?_
    by_cases hj : X+L ≤ j
    · have hiX := (mem_Icc.mp hi).2
      have he : j-i = L+(X-i)+(j-(X+L)) := by omega
      rw [he,pow_add,pow_add]
      ring
    · simp [farJump,hj]
  rw [joint_row_sum]
  rw [intervalIntegral.integral_congr (fun x _ => h x)]
  simp only [mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, ← realEndpoint_moment i (j-i) (mem_Icc.mp hi).1]
  ring

/-- Product after the common displacement has been removed, as a continuous
section on the closed interval. Its supremum measures both divisors together. -/
def jointSection (X N L : ℕ) (u b : ℕ → ℤ) : C(Set.Icc (0:ℝ) 1,ℝ) :=
  ⟨fun x => lowerSection X u x*upperSection X N L b x,by unfold lowerSection upperSection; fun_prop⟩

/-- Mass of the real-place section measure at displacement L. -/
theorem sectionMass (L : ℕ) :
    (∫ x in (0:ℝ)..1, x^L*(1-x)) = 1/(((L:ℝ)+1)*((L:ℝ)+2)) := by
  simp_rw [show ∀ x : ℝ, x^L*(1-x)=x^L-x^(L+1) by intro x; rw [pow_succ]; ring]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x^L) (g := fun x : ℝ => x^(L+1))
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    hilbertMoment_eq_integral_pow,hilbertMoment_eq_integral_pow,Nat.cast_succ]
  field_simp
  ring

/-- A moving effective endpoint recovers the unsmoothed prime error from the
full Weil row. Its real-place correction is exactly 1/(2m(m+1)). -/
theorem centeredWeilRow_single (m : ℕ+) :
    centeredWeilRow 1 m 0 (fun _ => 1) (fun j => if j=(m:ℕ) then 1 else 0) =
      1/(2*((m:ℕ):ℝ)*(((m:ℕ):ℝ)+1)) - psiRemainder m := by
  have hm : 1 ≤ (m:ℕ) := m.pos
  have hf (j : ℕ) : farJump 1 0 (fun i => if i=(m:ℕ) then 1 else 0) j =
      (if j=(m:ℕ) then 1 else 0) := by
    by_cases h : j=(m:ℕ)
    · subst j; simp [farJump,hm]
    · simp [farJump,h]
  have hnat : 1+((m:ℕ)-1) = m := by omega
  have hreal : (((m:ℕ)-1:ℕ):ℝ)+1 = (m:ℕ) := by rw [Nat.cast_sub hm,Nat.cast_one]; ring
  have hr := realEndpoint_moment 1 ((m:ℕ)-1) Nat.zero_lt_one
  simp only [sum_range_one,pow_zero,one_pow,mul_one,sectionMass,hreal] at hr
  have hs : (((m:ℕ)-1:ℕ):ℝ)+2 = ((m:ℕ):ℝ)+1 := by linarith only [hreal]
  rw [hs] at hr
  have htail : tailPotential (Icc 1 (m:ℕ)) 1 - (3/(4*(1:ℝ)) - Real.log (2*Real.pi)) =
      realEndpoint 1 ((m:ℕ)-1) - psiRemainder m := by
    rw [realEndpoint,hnat,psiRemainder]
    change _ = tailPotential _ _ - _ - (chebyshev (m:ℕ)-(m:ℝ))
    simp only [Nat.cast_one,Nat.div_one,div_one]
    ring
  have hvalue : realEndpoint 1 ((m:ℕ)-1) = 1/(2*((m:ℕ):ℝ)*(((m:ℕ):ℝ)+1)) := by
    rw [show 1/(2*((m:ℕ):ℝ)*(((m:ℕ):ℝ)+1)) = (1/(((m:ℕ):ℝ)*(((m:ℕ):ℝ)+1)))/2 by
      simp only [div_eq_mul_inv,mul_inv_rev,one_mul,mul_assoc]]
    linarith only [hr]
  rw [hvalue] at htail
  simp only [centeredWeilRow,fractionalBoundary,hf,Icc_self,sum_singleton,Int.cast_one,
    Nat.cast_one,Nat.div_one,div_one,sub_self,mul_zero,sum_const_zero,sub_zero,one_mul]
  simp [apply_ite,ite_mul,hm]
  simpa using htail

/-- Pairing with a continuous completed section. The clamping map only extends
the integrand outside the interval of integration. -/
def realSectionTrace (L : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) : ℝ :=
  ∫ x in (0:ℝ)..1, x^L*(1-x)*P (Set.projIcc 0 1 zero_le_one x)

theorem jointGraphHeight_trace (X N L : ℕ) (u b : ℕ → ℤ) :
    2*jointGraphHeight X N L u b = realSectionTrace L (jointSection X N L u b) := by
  rw [jointGraphHeight_sections,realSectionTrace]
  apply intervalIntegral.integral_congr
  intro x hx
  have h : x ∈ Set.Icc (0:ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using hx
  change _ = x^L*(1-x)*jointSection X N L u b (Set.projIcc 0 1 zero_le_one x)
  rw [Set.projIcc_of_mem zero_le_one h]
  rfl

private theorem trace_bound (L : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) :
    |realSectionTrace L P| ≤ ‖P‖ / (((L:ℝ)+1)*((L:ℝ)+2)) := by
  let G (x : ℝ) := P (Set.projIcc 0 1 zero_le_one x)
  have hG : Continuous G := P.continuous.comp continuous_projIcc
  have hw : Continuous (fun x : ℝ => x^L*(1-x)) := by fun_prop
  change |∫ x in (0:ℝ)..1, x^L*(1-x)*G x| ≤ _
  rw [← Real.norm_eq_abs]
  calc _ ≤ ∫ x in (0:ℝ)..1, ‖x^L*(1-x)*G x‖ :=
         intervalIntegral.norm_integral_le_integral_norm (by norm_num)
       _ ≤ ∫ x in (0:ℝ)..1, (x^L*(1-x))*‖P‖ := by
         apply intervalIntegral.integral_mono_on (by norm_num) ((hw.mul hG).norm.intervalIntegrable _ _)
           ((hw.mul continuous_const).intervalIntegrable _ _)
         intro x hx
         have hn := mul_nonneg (pow_nonneg hx.1 L) (sub_nonneg.mpr hx.2)
         change ‖x^L*(1-x)*G x‖ ≤ x^L*(1-x)*‖P‖
         rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hn]
         exact mul_le_mul_of_nonneg_left (P.norm_coe_le_norm _) hn
       _ = _ := by rw [intervalIntegral.integral_mul_const,sectionMass]; ring

/-- A reciprocal-square bound on the joint mixed height for every conductor,
gap and pair of signed integer divisors, using just the glued section norm. -/
theorem jointGraphHeight_bound (X N L : ℕ) (u b : ℕ → ℤ) :
    |2*jointGraphHeight X N L u b| ≤
      ‖jointSection X N L u b‖ / (((L:ℝ)+1)*((L:ℝ)+2)) := by
  rw [jointGraphHeight_trace]
  exact trace_bound _ _

/-- Uniform distance from the finite graph pairing to any completed section.
Only the supremum error of the product enters, allowing both divisors to vary. -/
theorem jointGraphHeight_distance (X N L : ℕ) (u b : ℕ → ℤ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) :
    |2*jointGraphHeight X N L u b-realSectionTrace L P| ≤
      ‖jointSection X N L u b-P‖ / (((L:ℝ)+1)*((L:ℝ)+2)) := by
  let Q := jointSection X N L u b
  have hI (F : C(Set.Icc (0:ℝ) 1,ℝ)) : IntervalIntegrable
      (fun x : ℝ => x^L*(1-x)*F (Set.projIcc 0 1 zero_le_one x)) volume 0 1 :=
    (Continuous.mul (by fun_prop) (F.continuous.comp continuous_projIcc)).intervalIntegrable _ _
  have he : realSectionTrace L (Q-P) = realSectionTrace L Q-realSectionTrace L P := by
    simp only [realSectionTrace,ContinuousMap.sub_apply]
    rw [← intervalIntegral.integral_sub (hI Q) (hI P)]
    exact intervalIntegral.integral_congr fun x _ => mul_sub _ _ _
  rw [jointGraphHeight_trace]
  change |realSectionTrace L Q-realSectionTrace L P| ≤ _
  rw [← he]
  exact trace_bound _ _

/-- The opposing upper section can be prescribed by any integral polynomial.
Its coefficients are the actual jumps at consecutive conductors, starting at X+L. -/
theorem upperSection_of_integer_polynomial (X : ℕ+) (L : ℕ) (p : Polynomial ℤ) :
    let N := (X:ℕ)+L+p.natDegree
    let b := fun j : ℕ => p.coeff (j-((X:ℕ)+L))
    ∀ x : ℝ, upperSection X N L b x = p.eval₂ (Int.castRingHom ℝ) x := by
  intro N b x
  let T := (X:ℕ)+L
  have hT : 1 ≤ T := Nat.le_trans X.pos (Nat.le_add_right _ _)
  have hj (j : ℕ) : (farJump X L b j:ℝ)*x^(j-T) =
      if T≤j then (p.coeff (j-T):ℝ)*x^(j-T) else 0 := by
    change ((if T≤j then p.coeff (j-T) else 0 : ℤ):ℝ)*x^(j-T) = _
    by_cases h : T≤j <;> simp [h]
  change (∑ j ∈ Icc 1 N, (farJump X L b j:ℝ)*x^(j-T)) = _
  simp only [hj,← sum_filter,Polynomial.eval₂_eq_sum_range]
  refine sum_nbij' (i := fun j => j-T) (j := fun k => T+k) ?_ ?_ ?_ ?_ ?_
  · intro j hj'
    have hjN := (mem_Icc.mp (mem_filter.mp hj').1).2
    have hTj := (mem_filter.mp hj').2
    apply mem_range.mpr
    change j ≤ T+p.natDegree at hjN
    omega
  · intro k hk
    have hk' := mem_range.mp hk
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨by omega,by change T+k ≤ T+p.natDegree; omega⟩,by omega⟩
  · intro j hj'
    have := (mem_filter.mp hj').2
    omega
  · intro k _
    omega
  · intro j _
    rfl

/-- Integral section of the lower divisor before evaluation at the real place. -/
def lowerSectionPolynomial (X : ℕ) (u : ℕ → ℤ) : Polynomial ℤ :=
  ∑ i ∈ Icc 1 X, Polynomial.C (u i)*Polynomial.X^(X-i)*(∑ a ∈ range i, Polynomial.X^a)^2

private theorem lowerSectionPolynomial_eval (X : ℕ) (u : ℕ → ℤ) (x : ℝ) :
    (lowerSectionPolynomial X u).eval₂ (Int.castRingHom ℝ) x = lowerSection X u x := by
  simp only [lowerSectionPolynomial,lowerSection,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,
    Polynomial.eval₂_pow,Polynomial.eval₂_C,Polynomial.eval₂_X]
  rfl

/-- Clearing the squared geometric denominator exposes the pair of opposite
exponents belonging to each conductor, with their common center subtracted. -/
theorem lowerSectionPolynomial_opposites (X : ℕ) (u : ℕ → ℤ) :
    (1-Polynomial.X)^2*lowerSectionPolynomial X u =
      ∑ i ∈ Icc 1 X, Polynomial.C (u i)*
        (Polynomial.X^(X-i)-2*Polynomial.X^X+Polynomial.X^(X+i)) := by
  let Z : Polynomial ℤ := Polynomial.X
  rw [lowerSectionPolynomial,mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hd : X-i+i = X := Nat.sub_add_cancel (mem_Icc.mp hi).2
  have he : Z^(X-i)*Z^i = Z^X := by rw [← pow_add,hd]
  change (1-Z)^2*(Polynomial.C (u i)*Z^(X-i)*(∑ a ∈ range i, Z^a)^2) = _
  calc _ = Polynomial.C (u i)*Z^(X-i)*((∑ a ∈ range i, Z^a)*(1-Z))^2 := by ring
       _ = _ := by
         rw [geom_sum_mul_neg]
         change Polynomial.C (u i)*Z^(X-i)*(1-Z^i)^2 =
           Polynomial.C (u i)*(Z^(X-i)-2*Z^X+Z^(X+i))
         rw [pow_add Z X i,← he]
         ring

/-- Each multiplicity is recovered by a single coefficient of the second
difference of the upper section. Signed gluing loses no lower divisor. -/
theorem recover_lower_multiplicity (X : ℕ) (u : ℕ → ℤ) {i : ℕ} (hi : i ∈ Icc 1 X) :
    ((1-Polynomial.X)^2*lowerSectionPolynomial X u).coeff (X-i) = u i := by
  rw [lowerSectionPolynomial_opposites,Polynomial.finsetSum_coeff]
  obtain ⟨hi0,hiX⟩ := mem_Icc.mp hi
  have hmid : X-i ≠ X := by omega
  have he (j : ℕ) (hj : j ∈ Icc 1 X) :
      (Polynomial.C (u j)*(Polynomial.X^(X-j)-2*Polynomial.X^X+Polynomial.X^(X+j))).coeff (X-i) =
      if j=i then u i else 0 := by
    have hjX := (mem_Icc.mp hj).2
    have htop : X-i ≠ X+j := by omega
    simp only [Polynomial.coeff_C_mul,Polynomial.coeff_add,Polynomial.coeff_sub,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_X_pow,if_neg hmid,if_neg htop,mul_zero,sub_zero,add_zero]
    by_cases h : j=i
    · subst j; simp
    · have hdiff : X-i ≠ X-j := by omega
      simp [hdiff,h]
  rw [sum_congr rfl he]
  simp [hi]

/-- An integral dual section has strictly positive mass precisely when at
least one lower multiplicity survives. This holds at every displacement. -/
theorem dual_section_strict_iff (X L : ℕ) (u : ℕ → ℤ) :
    (0 < ∫ x in (0:ℝ)..1, x^L*(1-x)*(lowerSection X u x)^2) ↔
      ∃ i ∈ Icc 1 X, u i ≠ 0 := by
  constructor
  · intro h
    by_contra hz
    push Not at hz
    have hu (x : ℝ) : lowerSection X u x = 0 :=
      sum_eq_zero fun i hi => by simp only [hz i hi,Int.cast_zero,zero_mul]
    simp [hu] at h
  · rintro ⟨i,hi,hui⟩
    let p := lowerSectionPolynomial X u
    let q := p.map (Int.castRingHom ℝ)
    have hp : p ≠ 0 := by
      intro h
      have he := recover_lower_multiplicity X u hi
      change ((1-Polynomial.X)^2*p).coeff (X-i) = u i at he
      rw [h,mul_zero,Polynomial.coeff_zero] at he
      exact hui he.symm
    have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff (f := Int.castRingHom ℝ) Int.cast_injective).mpr hp
    have hpoint : ∃ x ∈ Set.Ioo (0:ℝ) 1, q.eval x ≠ 0 := by
      by_contra h
      push Not at h
      exact hq (q.eq_zero_of_infinite_isRoot ((Set.Ioo_infinite (by norm_num : (0:ℝ)<1)).mono h))
    obtain ⟨x,hx,hxq⟩ := hpoint
    have hxu : lowerSection X u x ≠ 0 := by
      change (p.map (Int.castRingHom ℝ)).eval x ≠ 0 at hxq
      rwa [Polynomial.eval_map,lowerSectionPolynomial_eval] at hxq
    apply intervalIntegral.integral_pos (by norm_num)
    · unfold lowerSection; fun_prop
    · intro y hy
      exact mul_nonneg (mul_nonneg (pow_nonneg hy.1.le _) (sub_nonneg.mpr hy.2)) (sq_nonneg _)
    · exact ⟨x,⟨hx.1.le,hx.2.le⟩,mul_pos (mul_pos (pow_pos hx.1 _) (sub_pos.mpr hx.2)) (sq_pos_of_ne_zero hxu)⟩

/-- Every signed lower divisor has an integral upper dual giving exactly the
square of its own section in the common gauge. This applies at every gap. -/
theorem exists_effective_integral_dual (X : ℕ+) (L : ℕ) (u : ℕ → ℤ) :
    ∃ (N : ℕ) (b : ℕ → ℤ), (∀ x : ℝ, upperSection X N L b x = lowerSection X u x) ∧
      2*jointGraphHeight X N L u b = (∫ x in (0:ℝ)..1, x^L*(1-x)*(lowerSection X u x)^2) ∧
      0 ≤ jointGraphHeight X N L u b := by
  let p := lowerSectionPolynomial X u
  let N := (X:ℕ)+L+p.natDegree
  let b := fun j : ℕ => p.coeff (j-((X:ℕ)+L))
  have hdual (x : ℝ) : upperSection X N L b x = lowerSection X u x := by
    rw [show upperSection X N L b x = p.eval₂ (Int.castRingHom ℝ) x from
      upperSection_of_integer_polynomial X L p x]
    exact lowerSectionPolynomial_eval X u x
  have he := jointGraphHeight_sections X N L u b
  simp only [hdual,← sq] at he
  refine ⟨N,b,hdual,he,?_⟩
  have hnonneg : 0 ≤ 2*jointGraphHeight X N L u b := by
    rw [he]
    exact intervalIntegral.integral_nonneg (by norm_num) fun x hx =>
      mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (sub_nonneg.mpr hx.2)) (sq_nonneg _)
  linarith only [hnonneg]

#print axioms upperSection_of_integer_polynomial
#print axioms centeredWeilRow_single
#print axioms recover_lower_multiplicity
#print axioms dual_section_strict_iff
#print axioms exists_effective_integral_dual
#print axioms jointGraphHeight_sections
#print axioms jointGraphHeight_distance
#print axioms jointGraphHeight_bound

end GaloisForLFunctions.SignedArithmeticCorrespondences
