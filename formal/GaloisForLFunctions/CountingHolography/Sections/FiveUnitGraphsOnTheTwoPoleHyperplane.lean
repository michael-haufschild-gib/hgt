import GaloisForLFunctions.CountingHolography.Sections.FourSquareGraphsWithBothPoleDegreesZero
import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates

/-!
# Five unit graphs on the two-pole hyperplane

After scaling the middle of three negative square-root conductors to one,
write the two positive roots as u, v and the negative ones as x, 1, z.
Both endpoint dipoles have bounded transform on the entire closed strip,
uniformly in their separation.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Complex Finset Zeta23 SquareRootThreshold SurfaceOfSpecZ ArithmeticOrientationGeometry
open ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge ArithmeticScatteringHolography

private theorem interlaces {u v x y z : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : u+v=x+y+z) (hm : 1/u+1/v=1/x+1/y+1/z) : u < x ∧ x < v := by
  let D := x*y+x*z+y*z
  have hD : 0 < D := by dsimp only [D]; positivity
  have he : D*(u*v)=(u+v)*x*y*z := by
    field_simp [hu.ne',hv.ne',hx.ne',hy.ne',hz.ne'] at hm
    dsimp only [D]
    linarith only [hm]
  have hprod : D*((x-u)*(x-v)) = -(x^2*(y^2+y*z+z^2)) := by
    calc _ = D*(x^2-x*(u+v))+D*(u*v) := by ring
      _ = _ := by rw [he,hp]; dsimp only [D]; ring
  have hh : D*((x-u)*(x-v)) < 0 := hprod.trans_lt (neg_neg_of_pos (by positivity))
  have hpair : (x-u)*(x-v) < 0 := lt_of_not_ge fun h => hh.not_ge (mul_nonneg hD.le h)
  rcases mul_neg_iff.mp hpair with h | h
  · exact ⟨sub_pos.mp h.1,sub_neg.mp h.2⟩
  · linarith only [h.1,h.2,huv]

/-- The shorter and longer dipole widths multiplied by their respective
boundary exponentials are both at most twelve. -/
theorem fiveRoot_dipole_bounds {u v x z : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hx : 0 < x) (hx1 : x ≤ 1) (hz1 : 1 ≤ z)
    (hp : u+v=x+1+z) (hm : 1/u+1/v=1/x+1+1/z) :
    u < x ∧ z < v ∧ 2*Real.log (x/u)/u ≤ 12 ∧ 2*Real.log (v/z)*v ≤ 12 := by
  have hv := hu.trans_le huv
  have hz := zero_lt_one.trans_le hz1
  have hlo := (interlaces hu hv huv hx one_pos hz hp (by simpa only [div_one] using hm)).1
  have hhi := (interlaces hu hv huv hz one_pos hx (by linarith only [hp]) (by
    rw [div_one]; linarith only [hm])).2
  have hrec : 1/u-1/x ≤ 2 := by
    have hz' := one_div_le_one_div_of_le one_pos hz1
    rw [div_one] at hz'
    linarith only [hm,hz',one_div_nonneg.mpr hv.le]
  have hratio : x/u-1 ≤ 2*x := by
    have hh := mul_le_mul_of_nonneg_right hrec hx.le
    have he : (1/u-1/x)*x=x/u-1 := by field_simp
    rw [he] at hh
    exact hh
  have hxu : x/u ≤ 3 := by linarith only [hratio,hx1]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hu)
  have hprice := div_le_div_of_nonneg_right (hlog.trans hratio) hu.le
  have hg : v-z ≤ 2 := by linarith only [hp,hx1,hu]
  have hvz : v/z ≤ 3 := (div_le_iff₀ hz).mpr (by linarith only [hg,hz1])
  have hlog' := Real.log_le_sub_one_of_pos (div_pos hv hz)
  have hlog2 : Real.log (v/z) ≤ 2/z := hlog'.trans (by
    rw [div_sub_one hz.ne']
    exact div_le_div_of_nonneg_right hg hz.le)
  refine ⟨hlo,hhi,?_,?_⟩
  · have e1 : 2*Real.log (x/u)/u = 2*(Real.log (x/u)/u) := by ring
    have e2 : 2*x/u = 2*(x/u) := by ring
    linarith only [hprice,hxu,e1,e2]
  · have e3 : 2*Real.log (v/z)*v = 2*(Real.log (v/z)*v) := by ring
    have e4 : 2/z*v = 2*(v/z) := by ring
    linarith only [mul_le_mul_of_nonneg_right hlog2 hv.le,hvz,e3,e4]

/-- The signed exponential multiplier of two unit graphs against three,
normalized at the middle negative root. -/
def fiveRootMultiplier (u v x z : ℝ) (w : ℂ) :=
  (Complex.exp (w*(2*Real.log u:ℝ))-Complex.exp (w*(2*Real.log x:ℝ)))+
    (Complex.exp (w*(2*Real.log v:ℝ))-Complex.exp (w*(2*Real.log z:ℝ)))-1

/-- Uniform closure of the five-graph multiplier on the two spectral
boundary lines and everywhere between them. -/
theorem fiveRootMultiplier_bound {u v x z : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hx : 0 < x) (hx1 : x ≤ 1) (hz1 : 1 ≤ z)
    (hp : u+v=x+1+z) (hm : 1/u+1/v=1/x+1+1/z)
    {w : ℂ} (hw : |w.re| ≤ 1/2) :
    ‖fiveRootMultiplier u v x z w‖ ≤ 1+24*‖w‖ := by
  obtain ⟨hux,hzv,hl,hh⟩ := fiveRoot_dipole_bounds hu huv hx hx1 hz1 hp hm
  have hz := zero_lt_one.trans_le hz1
  have hv := hu.trans_le huv
  have hlow := norm_cexp_sub_le (z := -w) (by simpa only [Complex.neg_re,abs_neg] using hw)
    (s := -(2*Real.log x)) (t := -(2*Real.log u))
    (by linarith only [Real.log_nonpos hx.le hx1])
    (by linarith only [Real.log_le_log hu hux.le])
  have hhigh := norm_cexp_sub_le hw (s := 2*Real.log z) (t := 2*Real.log v)
    (mul_nonneg two_pos.le (Real.log_nonneg hz1)) (mul_le_mul_of_nonneg_left (Real.log_le_log hz hzv.le) two_pos.le)
  rw [show -(2*Real.log u)/2= -Real.log u by ring,Real.exp_neg,Real.exp_log hu,
    show -(2*Real.log u)- -(2*Real.log x)=2*Real.log (x/u) by rw [Real.log_div hx.ne' hu.ne']; ring,
    norm_neg] at hlow
  simp only [Complex.ofReal_neg,neg_mul_neg] at hlow
  rw [show 2*Real.log v/2=Real.log v by ring,Real.exp_log hv,
    show 2*Real.log v-2*Real.log z=2*Real.log (v/z) by rw [Real.log_div hv.ne' hz.ne']; ring] at hhigh
  have h₁ := mul_le_mul_of_nonneg_left hl (norm_nonneg w)
  have h₂ := mul_le_mul_of_nonneg_left hh (norm_nonneg w)
  unfold fiveRootMultiplier
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  have ht := norm_add_le (Complex.exp (w*(2*Real.log u:ℝ))-Complex.exp (w*(2*Real.log x:ℝ)))
    (Complex.exp (w*(2*Real.log v:ℝ))-Complex.exp (w*(2*Real.log z:ℝ)))
  have e5 : ‖w‖*(2*Real.log (x/u))*u⁻¹ = ‖w‖*(2*Real.log (x/u)/u) := by ring
  have e6 : ‖w‖*(2*Real.log (v/z))*v = ‖w‖*(2*Real.log (v/z)*v) := by ring
  linarith only [ht,hlow,hhigh,h₁,h₂,e5,e6]

/-- The same quadratic spectral envelope works for every normalized
five-graph multiplier. -/
theorem summable_quadratic_lag_envelope {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    Summable fun z : ℂ => ‖lagCoeff Z b z‖*(1+24*‖z‖)^2 := by
  let C := Real.exp w*bumpDecayConstant b^2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) _
    ((summable_indicator_mult_div_sq Z hZ).mul_left (625*C))
  intro z
  let M := Z.carrier.indicator (fun t => (Z.mult t:ℝ)) (1/2+z)
  let y := 1+|z.im|
  have hM : 0 ≤ M := Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) _
  have hy : 0 < y := by dsimp only [y]; positivity
  change ‖lagCoeff Z b z‖*(1+24*‖z‖)^2 ≤ (625*C)*(M/y^2)
  by_cases he : lagCoeff Z b z = 0
  · rw [he,norm_zero,zero_mul]
    positivity
  have hz := abs_re_le_of_lagCoeff_ne_zero he
  have hnorm : 1+24*‖z‖ ≤ 25*y := by
    dsimp only [y]
    linarith only [Complex.norm_le_abs_re_add_abs_im z,hz,abs_nonneg z.im]
  have hd : ‖lagCoeff Z b z‖ ≤ M*C/y^4 := norm_lagCoeff_le_decay Z hb hw hbs z
  refine (mul_le_mul hd (pow_le_pow_left₀ (by positivity) hnorm 2) (sq_nonneg _) (by positivity)).trans_eq ?_
  field_simp [hy.ne'] <;> ring

private def exponentialSum {ι : Type*} [Fintype ι] (v c : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, (c i:ℂ)*Complex.exp (z*(v i:ℂ))

private theorem trace_form {ι : Type*} [Fintype ι] (v c : ι → ℝ) :
    (∑ i, (∑ j, realSplineTrace (v i-v j)*c j)*c i) =
    (∑' z : ℂ, lagCoeff zetaZeroConfig (boxSpline 1 3) z *
      exponentialSum v c z * exponentialSum v c (-z)).re := by
  let b := boxSpline 1 3
  let D := lagCoeff zetaZeroConfig b
  let S := lagStructure zetaZeroConfig b
  have hz (u : ℝ) := lagStructure_eq_tsum_lagCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_boxSpline_two (le_refl 3)) (boxSpline_support (r := 1) one_pos 3) u
  have hs (u : ℝ) : HasSum (fun z : ℂ => D z*Complex.exp (z*(u:ℂ))) (S u) := by
    rw [show S u = _ from (hz u).2]
    exact (hz u).1.hasSum
  have he (z : ℂ) : D z*exponentialSum v c z*exponentialSum v c (-z) =
      ∑ i, ∑ j, D z*Complex.exp (z*((v i-v j:ℝ):ℂ))*(c j:ℂ)*(c i:ℂ) := by
    unfold exponentialSum
    rw [mul_assoc,Finset.sum_mul_sum,Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have harg : z*((v i-v j:ℝ):ℂ) = z*(v i:ℂ)+(-z)*(v j:ℂ) := by push_cast; ring
    rw [harg,Complex.exp_add]
    ring
  have hadd : HasSum (fun z : ℂ => ∑ i, ∑ j, D z*Complex.exp (z*((v i-v j:ℝ):ℂ))*(c j:ℂ)*(c i:ℂ))
      (∑ i, ∑ j, S (v i-v j)*(c j:ℂ)*(c i:ℂ)) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ => ((hs (v i-v j)).mul_right _).mul_right _
  change _ = (∑' z : ℂ, D z*exponentialSum v c z*exponentialSum v c (-z)).re
  simp_rw [he]
  rw [hadd.tsum_eq]
  have hS (u : ℝ) : (S u).re = realSplineTrace u := by
    change (lagStructure zetaZeroConfig (boxSpline 1 3) u).re = _
    simp only [← orbitCorr_eq_re_lagStructure_spline,RenormalizedIntersectionTheory.orbitCorr_splineCycle_eq,
      realSplineTrace]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,hS,sum_mul]

private def fiveLags (u v x z : ℝ) : Fin 5 → ℝ :=
  ![2*Real.log u,2*Real.log v,2*Real.log x,0,2*Real.log z]

private def fiveSigns : Fin 5 → ℝ := ![1,1,-1,-1,-1]

/-- Signed spline degree at square-root conductors u, v, x, 1, z with
the first two positive and the last three negative. -/
def fiveUnitTraceForm (u v x z : ℝ) :=
  let t := fiveLags u v x z
  ∑ i, (∑ j, realSplineTrace (t i-t j)*fiveSigns j)*fiveSigns i

private theorem exp_five (u v x z : ℝ) (w : ℂ) :
    exponentialSum (fiveLags u v x z) fiveSigns w = fiveRootMultiplier u v x z w := by
  simp [exponentialSum,fiveLags,fiveSigns,Fin.sum_univ_succ,fiveRootMultiplier] <;> ring

/-- The real Weil form of every balanced two-against-three configuration
is uniformly bounded as either or both endpoint ratios tend to infinity. -/
theorem fiveUnitTraceForm_bounded :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u v x z : ℝ}, 0 < u → u ≤ v → 0 < x → x ≤ 1 → 1 ≤ z →
      u+v=x+1+z → 1/u+1/v=1/x+1+1/z →
      |fiveUnitTraceForm u v x z| ≤ K := by
  let D := lagCoeff zetaZeroConfig (boxSpline 1 3)
  let G := fun w : ℂ => ‖D w‖*(1+24*‖w‖)^2
  have hG : Summable G := summable_quadratic_lag_envelope temperedConfig_zetaZeroConfig
    (contDiff_boxSpline_two (le_refl 3)) (by norm_num) (boxSpline_support (r := 1) one_pos 3)
  refine ⟨∑' w, G w,tsum_nonneg fun w => mul_nonneg (norm_nonneg _) (sq_nonneg _),?_⟩
  intro u v x z hu huv hx hx1 hz1 hp hm
  unfold fiveUnitTraceForm
  rw [trace_form]
  simp_rw [exp_five]
  let P := fiveRootMultiplier u v x z
  have hb (w : ℂ) : ‖D w*P w*P (-w)‖ ≤ G w := by
    by_cases hD : D w = 0
    · simp only [hD,zero_mul,norm_zero,G,le_refl]
    have hw := abs_re_le_of_lagCoeff_ne_zero hD
    have h₁ := fiveRootMultiplier_bound hu huv hx hx1 hz1 hp hm hw
    have h₂ := fiveRootMultiplier_bound hu huv hx hx1 hz1 hp hm (w := -w)
      (by simpa only [Complex.neg_re,abs_neg] using hw)
    rw [norm_neg] at h₂
    rw [mul_assoc,norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (sq _).symm) (norm_nonneg _)
  have hsum := Summable.of_nonneg_of_le (fun w => norm_nonneg _) hb hG
  exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hb hG))

private def unitCoefficients : Fin 5 → ℤ := ![1,1,-1,-1,-1]

/-- Two positive unit graphs against three negative unit graphs, allowing
coincident labels. The degree bound is independent of the five conductors. -/
def fiveUnitDivisor {N : ℕ} (e : Fin 5 → Fin N) := integralGraphSum e unitCoefficients

theorem fiveUnitDivisor_degree_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ} (e : Fin 5 → Fin N),
      e 0 ≤ e 1 → e 2 ≤ e 3 → e 3 ≤ e 4 →
      positivePoleDegree (fiveUnitDivisor e) = 0 → negativePoleDegree (fiveUnitDivisor e) = 0 →
      |integerProbe N (fiveUnitDivisor e)| ≤ K := by
  obtain ⟨K,hK,h⟩ := fiveUnitTraceForm_bounded
  refine ⟨K,hK,fun {N} e huv hxy hyz hp hm => ?_⟩
  let r (i : Fin 5) := Real.sqrt ((e i:ℝ)+1)
  let y := r 3
  let R (i : Fin 5) := r i/y
  have hr (i : Fin 5) : 0 < r i := Real.sqrt_pos_of_pos (by positivity)
  have hy : 0 < y := hr 3
  have hR (i : Fin 5) : 0 < R i := div_pos (hr i) hy
  have hsort {i j : Fin 5} (hij : e i ≤ e j) : r i ≤ r j := by
    apply Real.sqrt_le_sqrt
    exact add_le_add (by exact_mod_cast (show (e i).val ≤ (e j).val from hij) : (e i:ℝ) ≤ e j) (le_refl 1)
  have hmid : R 3 = 1 := div_self hy.ne'
  have hp' : (∑ i, r i*(unitCoefficients i:ℝ)) = 0 := by
    simpa only [positivePoleDegree,fiveUnitDivisor,sum_integralGraphSum,r] using hp
  have hm' : (∑ i, (r i)⁻¹*(unitCoefficients i:ℝ)) = 0 := by
    simpa only [negativePoleDegree,fiveUnitDivisor,sum_integralGraphSum,r] using hm
  have hu0 : unitCoefficients 0 = 1 := rfl
  have hu1 : unitCoefficients 1 = 1 := rfl
  have hu2 : unitCoefficients 2 = -1 := rfl
  have hu3 : unitCoefficients 3 = -1 := rfl
  have hu4 : unitCoefficients 4 = -1 := rfl
  simp only [Fin.sum_univ_five,hu0,hu1,hu2,hu3,hu4,Int.cast_one,Int.cast_neg,mul_one,mul_neg] at hp' hm'
  have hsum : r 0+r 1=r 2+r 3+r 4 := by linarith only [hp']
  have hinv : (r 0)⁻¹+(r 1)⁻¹=(r 2)⁻¹+(r 3)⁻¹+(r 4)⁻¹ := by linarith only [hm']
  have hpR : R 0+R 1=R 2+1+R 4 := by
    simpa only [R,add_div,show r 3 / y = 1 from div_self hy.ne'] using congrArg (fun q : ℝ => q/y) hsum
  have hrec (i : Fin 5) : 1/R i=y*(r i)⁻¹ := by simp only [R]; rw [one_div_div,div_eq_mul_inv]
  have hone : y*(r 3)⁻¹=1 := mul_inv_cancel₀ hy.ne'
  have hmR : 1/R 0+1/R 1=1/R 2+1+1/R 4 := by
    simp only [hrec]
    calc _ = y*((r 0)⁻¹+(r 1)⁻¹) := (mul_add _ _ _).symm
      _ = _ := by rw [hinv,mul_add,mul_add,hone]
  have hb := h (hR 0) (div_le_div_of_nonneg_right (hsort huv) hy.le) (hR 2)
    ((div_le_one hy).mpr (hsort hxy)) ((one_le_div hy).mpr (hsort hyz)) hpR hmR
  let t := fiveLags (R 0) (R 1) (R 2) (R 4)
  have ht (i : Fin 5) : t i = 2*Real.log (R i) := by
    fin_cases i <;> simp [t,fiveLags,hmid]
  have hlog (i : Fin 5) : Real.log ((e i:ℝ)+1) = t i+2*Real.log y := by
    rw [ht]
    simp only [R,Real.log_div (hr i).ne' hy.ne',r,Real.log_sqrt (by positivity : 0 ≤ (e i:ℝ)+1)]
    ring
  have hd (i j : Fin 5) : Real.log ((e i:ℝ)+1)-Real.log ((e j:ℝ)+1) = t i-t j := by
    rw [hlog,hlog]; ring
  have hc (i : Fin 5) : (unitCoefficients i:ℝ)=fiveSigns i := by
    fin_cases i <;> norm_num [unitCoefficients,fiveSigns]
  rw [fiveUnitDivisor,integerProbe_integralGraphSum]
  simp_rw [hd,hc]
  exact hb

end GaloisForLFunctions.CountingHolography.Sections
