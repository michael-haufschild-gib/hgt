import GaloisForLFunctions.SignedArithmeticCorrespondences.EffectivityAcrossCompleteEndpointBlocks
import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# A positive measure for complete conductor blocks

Frullani's integral turns a pair of reflected graph offsets into a positive
Laplace density. Shifting an endpoint multiplies this density by a monomial.
The mixed graph curvature therefore extends to continuous sections on the
unit interval, with exact norm equal to the curvature of the unshifted block.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open MeasureTheory Set Finset HTGeometry
open scoped Topology

private def logCell (a t : ℝ) : ℝ :=
  (Real.exp (-(a*t))-Real.exp (-((a+1)*t)))/t

private theorem logCell_frullani (a : ℝ) (ha : 0 < a) :
    IntegrableOn (logCell a) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), logCell a t) = Real.log (a+1)-Real.log a := by
  let b := a+1
  have hb : 0 < b := by dsimp [b]; linarith
  have hc := integrableOn_frullani (a := (a:ℂ)) (b := (b:ℂ))
    (by simpa using ha) (by simpa using hb)
  have he := integral_frullani (a := (a:ℂ)) (b := (b:ℂ))
    (by simpa using ha) (by simpa using hb)
  have hf (t : ℝ) : logCell a t =
      ((Complex.exp (-((a:ℂ)*t))-Complex.exp (-((b:ℂ)*t)))/(t:ℂ)).re := by
    simp [logCell,b,Complex.exp_re]
  constructor
  · change Integrable (logCell a) (volume.restrict (Ioi 0))
    exact hc.re.congr (Filter.Eventually.of_forall fun t => (hf t).symm)
  · simp_rw [hf]
    calc _ = (∫ t in Ioi (0:ℝ),
              (Complex.exp (-((a:ℂ)*t))-Complex.exp (-((b:ℂ)*t)))/(t:ℂ)).re := integral_re hc
         _ = _ := ?_
    rw [he,Complex.sub_re,Complex.log_re,Complex.log_re]
    change Real.log ‖(b:ℂ)‖-Real.log ‖(a:ℂ)‖ = Real.log b-Real.log a
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,abs_of_pos hb]

/-- The logarithmic increment at one positive conductor is the integral
of its two adjacent exponential rates. -/
theorem integral_log_increment (a : ℝ) (ha : 0<a) :
    (∫ t in Set.Ioi (0:ℝ), (Real.exp (-(a*t))-Real.exp (-((a+1)*t)))/t) =
      Real.log (a+1)-Real.log a := (logCell_frullani a ha).2

private def reflectedCell (a z t : ℝ) : ℝ :=
  logCell (a+z) t+logCell (a-z) t-2*logCell a t

private theorem reflected_integral {a z : ℝ} (ha : 1 ≤ a) (hz : -1 < z ∧ z < 1) :
    IntegrableOn (reflectedCell a z) (Ioi 0) ∧
    (∫ t in Ioi (0:ℝ), reflectedCell a z t) =
      Real.log (1-(z/(a+1))^2)-Real.log (1-(z/a)^2) := by
  have hp := logCell_frullani (a+z) (by linarith [hz.1])
  have hm := logCell_frullani (a-z) (by linarith [hz.2])
  have h0 := logCell_frullani a (by linarith)
  have hlog {v : ℝ} (hv : 1 ≤ v) :
      Real.log (1-(z/v)^2) = Real.log (v+z)+Real.log (v-z)-2*Real.log v := by
    have hpos : 0 < v := by linarith
    have hp' : 0 < v+z := by linarith [hz.1]
    have hm' : 0 < v-z := by linarith [hz.2]
    rw [show 1-(z/v)^2 = ((v+z)*(v-z))/v^2 by field_simp; ring,
      Real.log_div (mul_pos hp' hm').ne' (pow_ne_zero _ hpos.ne'),
      Real.log_mul hp'.ne' hm'.ne',Real.log_pow]
    norm_num
  refine ⟨(hp.1.add hm.1).sub (h0.1.const_mul 2),?_⟩
  simp only [reflectedCell]
  rw [integral_sub (f := fun t => logCell (a+z) t + logCell (a-z) t)
      (g := fun t => 2*logCell a t) (hp.1.add hm.1) (h0.1.const_mul 2),integral_add hp.1 hm.1,
    integral_const_mul,hp.2,hm.2,h0.2,hlog (v := a+1) (by linarith),hlog ha]
  rw [show a+z+1 = a+1+z by ring,show a-z+1 = a+1-z by ring]
  ring

private theorem reflected_formula (a z t : ℝ) :
    reflectedCell a z t =
      Real.exp (-(a*t)) * (1-Real.exp (-t)) *
      (Real.exp (z*t)+Real.exp (-(z*t))-2) / t := by
  have step (b : ℝ) : logCell b t = Real.exp (-(b*t))*(1-Real.exp (-t))/t := by
    rw [logCell,show -((b+1)*t) = -(b*t)+(-t) by ring,Real.exp_add]
    ring
  simp only [reflectedCell,step]
  rw [show -((a+z)*t) = -(a*t) + -(z*t) by ring,
    show -((a-z)*t) = -(a*t) + z*t by ring,Real.exp_add,Real.exp_add]
  ring

private theorem reflected_nonneg {a z t : ℝ} (ht : 0 < t) : 0 ≤ reflectedCell a z t := by
  rw [reflected_formula]
  have he := Real.exp_pos (z*t)
  have htwo : 0 ≤ Real.exp (z*t)+Real.exp (-(z*t))-2 := by
    rw [Real.exp_neg]
    apply nonneg_of_mul_nonneg_left (b := Real.exp (z*t)) _ he
    rw [sub_mul,add_mul,inv_mul_cancel₀ he.ne']
    nlinarith only [sq_nonneg (Real.exp (z*t)-1)]
  exact div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))) htwo) ht.le

/-- Twice the arithmetic curvature of a complete block is the mass of this density. -/
def blockDensity (d : ℕ+) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ range (d:ℕ), ∑ j ∈ range (d:ℕ), reflectedCell ((n:ℝ)+1) (offset d r j) t

/-- Exponential densities of the two reflected residue classes. The common
factor is the integral over one unit logarithmic increment. -/
theorem blockDensity_offsets (d : ℕ+) (n : ℕ) (t : ℝ) :
    blockDensity d n t = ((1-Real.exp (-t))/t) *
      ∑ r ∈ range (d:ℕ), ∑ j ∈ range (d:ℕ),
        (Real.exp (-((((n:ℝ)+1)+offset d r j)*t))+
         Real.exp (-((((n:ℝ)+1)-offset d r j)*t))-2*Real.exp (-(((n:ℝ)+1)*t))) := by
  simp only [blockDensity,mul_sum]
  refine sum_congr rfl fun r _ => sum_congr rfl fun j _ => ?_
  let a := (n:ℝ)+1
  let z := offset d r j
  change reflectedCell a z t = _ * (Real.exp (-((a+z)*t))+Real.exp (-((a-z)*t))-2*Real.exp (-(a*t)))
  rw [reflected_formula]
  rw [show -((a+z)*t) = -(a*t) + -(z*t) by ring,
    show -((a-z)*t) = -(a*t) + z*t by ring,Real.exp_add,Real.exp_add]
  ring

private theorem cell_offset {d r j : ℕ} (hr : r ∈ range d) (hj : j ∈ range d) :
    -1 < offset d r j ∧ offset d r j < 1 := offset_bounds (mem_range.mp hr) (mem_range.mp hj)

/-- Integrating the density recovers the second difference of the integral graph height. -/
theorem blockDensity_mass (d : ℕ+) (n : ℕ) :
    IntegrableOn (blockDensity d n) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), blockDensity d n t) =
        2*(blockHeight d (n+2)-2*blockHeight d (n+1)+blockHeight d n) := by
  have ha : 1 ≤ (n:ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hi (r : ℕ) (hr : r ∈ range (d:ℕ)) :
      IntegrableOn (fun t => ∑ j ∈ range (d:ℕ), reflectedCell ((n:ℝ)+1) (offset d r j) t)
        (Ioi 0) := integrable_finsetSum _ fun j hj => (reflected_integral ha (cell_offset hr hj)).1
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [block_curvature]
  unfold blockDensity
  rw [integral_finsetSum _ hi]
  refine sum_congr rfl fun r hr => ?_
  rw [integral_finsetSum _ fun j hj => (reflected_integral ha (cell_offset hr hj)).1]
  refine sum_congr rfl fun j hj => ?_
  simpa only [show (n:ℝ)+1+1=n+2 by ring] using (reflected_integral ha (cell_offset hr hj)).2

private theorem blockDensity_nonneg (d : ℕ+) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ blockDensity d n t :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => reflected_nonneg ht

private theorem blockDensity_shift (d : ℕ+) (n k : ℕ) (t : ℝ) :
    blockDensity d (n+k) t = Real.exp (-t)^k * blockDensity d n t := by
  simp only [blockDensity,mul_sum]
  refine sum_congr rfl fun r _ => sum_congr rfl fun j _ => ?_
  rw [reflected_formula,reflected_formula,← Real.exp_nat_mul]
  push_cast
  rw [show -(((n:ℝ)+k+1)*t) = (k:ℝ)*(-t) + -(((n:ℝ)+1)*t) by ring,Real.exp_add]
  ring

/-- The same bounded functional acts on the product of any two continuous
endpoint sections. On the positive integration ray its coordinate is exp(-t). -/
def sectionIntersection (d : ℕ+) (n : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) : ℝ :=
  (∫ t in Ioi (0:ℝ), blockDensity d n t *
    P ⟨Real.exp (-|t|),(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))⟩)/2

private def sectionCoordinate (t : ℝ) : Set.Icc (0:ℝ) 1 :=
  ⟨Real.exp (-|t|),(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))⟩

private theorem coord_continuous : Continuous sectionCoordinate :=
  (Real.continuous_exp.comp continuous_abs.neg).subtype_mk _

/-- The mass of the positive measure is its sharp bound on all continuous
sections. The constant section attains it for every conductor and modulus. -/
theorem sectionIntersection_bound (d : ℕ+) (n : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) :
    |sectionIntersection d n P| ≤
      (blockHeight d (n+2)-2*blockHeight d (n+1)+blockHeight d n)*‖P‖ := by
  have hm := blockDensity_mass d n
  let μ := volume.restrict (Ioi (0:ℝ))
  have hpos : ∀ᵐ t ∂μ, 0 ≤ blockDensity d n t :=
    (ae_restrict_mem measurableSet_Ioi).mono fun t ht => blockDensity_nonneg d n ht
  have hnorm : ∀ᵐ t ∂μ, ‖blockDensity d n t * P (sectionCoordinate t)‖ ≤ blockDensity d n t * ‖P‖ := by
    filter_upwards [hpos] with t ht
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (P.norm_coe_le_norm _) ht
  have hi : Integrable (fun t => blockDensity d n t * P (sectionCoordinate t)) μ :=
    (hm.1.mul_const ‖P‖).mono'
      (hm.1.aestronglyMeasurable.mul (P.continuous.comp coord_continuous).aestronglyMeasurable) hnorm
  have hb := (norm_integral_le_integral_norm (f := fun t => blockDensity d n t*P (sectionCoordinate t))
    (μ := μ)).trans (integral_mono_ae hi.norm (hm.1.mul_const ‖P‖) hnorm)
  change |(∫ t, blockDensity d n t * P (sectionCoordinate t) ∂μ)/2| ≤ _
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [Real.norm_eq_abs,integral_mul_const] at hb
  change |∫ t, blockDensity d n t * P (sectionCoordinate t) ∂μ| ≤ (∫ t in Ioi (0:ℝ), blockDensity d n t)*‖P‖ at hb
  rw [hm.2] at hb
  linarith only [hb]

theorem sectionIntersection_one (d : ℕ+) (n : ℕ) :
    sectionIntersection d n 1 = blockHeight d (n+2)-2*blockHeight d (n+1)+blockHeight d n := by
  simp only [sectionIntersection,ContinuousMap.one_apply,mul_one,(blockDensity_mass d n).2]
  ring

/-- The section of a signed collection of shifts. Equal powers add before evaluation. -/
def endpointPolynomial (S : Finset ℕ) (u : ℕ → ℝ) : C(Set.Icc (0:ℝ) 1,ℝ) :=
  ⟨fun x => ∑ i ∈ S, u i*(x:ℝ)^i, by fun_prop⟩

/-- The completed pairing on two endpoint polynomials is exactly the sum of
the mixed integral graph curvatures, including coincident total shifts. -/
theorem sectionIntersection_gluing (d : ℕ+) (n : ℕ) (S T : Finset ℕ) (u v : ℕ → ℝ) :
    sectionIntersection d n (endpointPolynomial S u * endpointPolynomial T v) =
      ∑ i ∈ S, ∑ j ∈ T, u i*v j*
        (blockHeight d (n+i+j+2)-2*blockHeight d (n+i+j+1)+blockHeight d (n+i+j)) := by
  let μ := volume.restrict (Ioi (0:ℝ))
  have hi (i j : ℕ) : Integrable (fun t => (u i*v j)*blockDensity d (n+i+j) t) μ :=
    (blockDensity_mass d _).1.const_mul _
  change (∫ t, blockDensity d n t *
    ((endpointPolynomial S u * endpointPolynomial T v) (sectionCoordinate t)) ∂μ)/2 = _
  have hp : (fun t => blockDensity d n t *
        ((endpointPolynomial S u * endpointPolynomial T v) (sectionCoordinate t))) =ᵐ[μ]
      fun t => ∑ i ∈ S, ∑ j ∈ T, (u i*v j)*blockDensity d (n+i+j) t := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have ht' : 0 ≤ t := le_of_lt ht
    simp only [ContinuousMap.mul_apply,endpointPolynomial,ContinuousMap.coe_mk,sectionCoordinate,
      abs_of_nonneg ht']
    rw [sum_mul_sum]
    simp only [mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Nat.add_assoc,blockDensity_shift,pow_add]
    ring
  rw [integral_congr_ae hp, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j,
    div_eq_iff (by norm_num : (2:ℝ) ≠ 0),sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi i j,sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  change u i*v j*(∫ t in Ioi (0:ℝ), blockDensity d (n+i+j) t) = _
  rw [(blockDensity_mass d _).2]
  ring

/-- On arbitrary increasing signed endpoint supports the modulus and conductor
enter only through 2d²/(n+1)³. The remaining cost is the supremum of the
product of the glued endpoint polynomials on the full unit interval. -/
theorem mixed_block_curvature_bound (d : ℕ+) (n : ℕ) (hn : 1 ≤ n)
    (S T : Finset ℕ) (u v : ℕ → ℝ) :
    |∑ i ∈ S, ∑ j ∈ T, u i*v j*
        (blockHeight d (n+i+j+2)-2*blockHeight d (n+i+j+1)+blockHeight d (n+i+j))| ≤
      2*((d:ℕ):ℝ)^2/((n:ℝ)+1)^3 * ‖endpointPolynomial S u * endpointPolynomial T v‖ := by
  rw [← sectionIntersection_gluing]
  exact (sectionIntersection_bound ..).trans
    (mul_le_mul_of_nonneg_right (block_curvature_bounds d n hn).2 (norm_nonneg _))

/-- Every real continuous section has an effective self-intersection. -/
theorem sectionIntersection_square_nonneg (d : ℕ+) (n : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) :
    0 ≤ sectionIntersection d n (P*P) := by
  unfold sectionIntersection
  apply div_nonneg _ (by norm_num)
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (blockDensity_nonneg d n ht) (mul_self_nonneg _)

#print axioms blockDensity_mass
#print axioms blockDensity_offsets
#print axioms sectionIntersection_gluing
#print axioms mixed_block_curvature_bound
#print axioms sectionIntersection_square_nonneg

end GaloisForLFunctions.SignedArithmeticCorrespondences
