import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SymmetricDilations.Comparison

/-! # Gaussian time dilations at inverse-square-root precision -/
open Real Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SymmetricDilations
noncomputable section

/-- Dilation increasing the inverse variance by h. -/
def scale (h : ℝ) : ℝ := (sqrt (1+h))⁻¹

theorem scale_bounds {h : ℝ} (hh : |h| ≤ 1/2) : scale h ∈ Icc (1/2:ℝ) 2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  have hp : 0 < 1+h := by linarith only [hl]
  have he := sq_sqrt hp.le
  have hpos := sqrt_pos.mpr hp
  have hl' : 1/2 ≤ sqrt (1+h) :=
    (le_sqrt (by norm_num) hp.le).mpr (by linarith only [hl])
  have hu' : sqrt (1+h) ≤ 2 :=
    (sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hu]⟩)
  rw [scale,←one_div]
  exact ⟨(le_div_iff₀ hpos).mpr (by linarith only [hu']),
    (div_le_iff₀ hpos).mpr (by linarith only [hl'])⟩

private theorem precision {h : ℝ} (hh : |h| ≤ 1/2) : (scale h)⁻¹^2=1+h := by
  rw [scale,inv_inv,sq_sqrt (by linarith only [(abs_le.mp hh).1])]

private theorem bernoulli {x : ℝ} (hx : 0≤x) (hu : x≤1) (m : ℕ) :
    1-(m:ℝ)*x ≤ (1-x)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hu)
    rw [pow_succ,Nat.cast_succ]
    nlinarith only [he,mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (sq_nonneg x)]

/-- Up to inverse-square-root changes in precision, opposite shifts
control the original probability with a constant independent of dimension. -/
theorem bounded_precision_price {ι : Type*} [Fintype ι] {h : ℝ}
    (hh : |h|≤1/2) (hsmall : (Fintype.card ι:ℝ)*h^2≤1/2)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.real E ≤ μ.real ((fun x : ι → ℝ => scale h • x) ⁻¹' E)+
      μ.real ((fun x : ι → ℝ => scale (-h) • x) ⁻¹' E) := by
  have hh' : |-h|≤1/2 := (abs_neg h).trans_le hh
  have ha : 0<scale h := (by norm_num : (0:ℝ)<1/2).trans_le (scale_bounds hh).1
  have hb : 0<scale (-h) := (by norm_num : (0:ℝ)<1/2).trans_le (scale_bounds hh').1
  apply gaussian_pair_mass ha hb (by rw [precision hh,precision hh']; ring) _ E hE
  let z := scale h*scale (-h)
  let m := Fintype.card ι
  have hz : 0<z := mul_pos ha hb
  have he : (z⁻¹)^2=1-h^2 := by
    dsimp only [z]
    rw [mul_inv_rev,mul_pow,precision hh,precision hh']
    ring
  have hu := (sq_abs h) ▸ pow_le_pow_left₀ (abs_nonneg h) hh 2
  have hB := bernoulli (sq_nonneg h) (by linarith only [hu]) m
  have hp : 1/2 ≤ (z^m)⁻¹^2 := by
    rw [←inv_pow,←pow_mul,pow_mul']
    rw [he]
    exact (by linarith only [hsmall] : 1/2 ≤ 1-(m:ℝ)*h^2).trans hB
  have hden : 0 < z^m := pow_pos hz _
  have hbound : (1/2:ℝ)*(z^m)^2 ≤ 1 := by
    rw [inv_pow] at hp
    simpa only [one_div] using (le_div_iff₀ (sq_pos_of_pos hden)).mp (by simpa only [one_div] using hp :
      1/2 ≤ 1/(z^m)^2)
  change z^m ≤ 4
  nlinarith only [hbound,sq_nonneg (z^m-1)]

/-- Precision and scale measure the same separations on the central band.
The constants are uniform for both rows and all Gaussian dimensions. -/
theorem scale_gap {h k : ℝ} (hh : |h|≤1/2) (hk : |k|≤1/2) :
    |h-k|/64 ≤ |scale h-scale k| ∧ |scale h-scale k| ≤ 16*|h-k| := by
  let a := scale h
  let b := scale k
  have ha : a∈Icc (1/2:ℝ) 2 := scale_bounds hh
  have hb : b∈Icc (1/2:ℝ) 2 := scale_bounds hk
  have ha₀ : 0<a := (by norm_num : (0:ℝ)<1/2).trans_le ha.1
  have hb₀ : 0<b := (by norm_num : (0:ℝ)<1/2).trans_le hb.1
  have hl : 1/4 ≤ a*b := by nlinarith only [mul_le_mul ha.1 hb.1 (by norm_num) ha₀.le]
  have hu : a*b ≤ 4 := by nlinarith only [mul_le_mul ha.2 hb.2 hb₀.le (by norm_num)]
  have he : (h-k)*(a*b)^2=(b-a)*(a+b) := by
    have ep : h-k=a⁻¹^2-b⁻¹^2 := by rw [precision hh,precision hk]; ring
    rw [ep]
    field_simp [ha₀.ne',hb₀.ne']
    <;> ring
  have hab := congrArg abs he
  rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_nonneg (add_nonneg ha₀.le hb₀.le),
    abs_sub_comm b a] at hab
  have h₁ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hl 2) (abs_nonneg (h-k))
  have h₂ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg ha₀.le hb₀.le) hu 2) (abs_nonneg (h-k))
  have h₃ := mul_le_mul_of_nonneg_left (add_le_add ha.1 hb.1) (abs_nonneg (a-b))
  have h₄ := mul_le_mul_of_nonneg_left (add_le_add ha.2 hb.2) (abs_nonneg (a-b))
  change |h-k|/64 ≤ |a-b| ∧ |a-b| ≤ 16*|h-k|
  constructor <;> linarith only [h₁,h₂,h₃,h₄,hab]

#print axioms bounded_precision_price
#print axioms scale_gap
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SymmetricDilations
