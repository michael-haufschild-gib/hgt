import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PrimeIntervalsOnTheRescaledConductor
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PeriodicQuotientCancellation
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PiecewiseSmoothnessOfTheDyadicSpline
import GaloisForLFunctions.RHTower.SqrtTelescopeSums

/-!
# The signed integral on a rescaled product shell

The quotient mesh depends on q and the conductor x only through q/x².
After x = t sqrt(q), the same mesh multiplies all product coefficients
at a given t. An eighth difference of the spline gives seven powers of
the real mesh size, also between integer conductors.
-/

noncomputable section
open Finset ArithmeticFunction MeasureTheory
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Finite mesh in the outer quotient. The support cutoff decides how far j must run. -/
def quotientMeshProfile (b : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ range b, (dyadicSpline (j*h) - dyadicSpline ((j+1:ℕ)*h)) * centeredPrimeWeight 1 j

/-- The normalized integer horizon pair is the restriction of the real mesh. -/
theorem unitHorizonPair_real_profile {n q b : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hb : splineHorizon n < q*b) :
    (n:ℝ)^2 * unitHorizonPair n q = n * quotientMeshProfile b (q/(n:ℝ)^2) := by
  rw [unitHorizonPair_eq_quotient_blocks hn hq hb, quotientMeshProfile, mul_sum, mul_sum]
  apply sum_congr rfl
  intro j _
  unfold sampledSpline
  push_cast
  have hn0 : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have e1 : (q:ℝ)*j/(n:ℝ)^2 = j*((q:ℝ)/(n:ℝ)^2) := by ring
  have e2 : (q:ℝ)*(j+1)/(n:ℝ)^2 = (j+1)*((q:ℝ)/(n:ℝ)^2) := by ring
  rw [e1,e2]
  field_simp

/-- The seventh power of the step is uniform for real conductor rescaling. -/
theorem quotientMeshProfile_seventh :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → 7*h < Real.exp (-8) →
      ∀ b : ℕ, 4*Real.exp 8 < b*h → |quotientMeshProfile b h| ≤ C*h^7 := by
  obtain ⟨A,hA,ha⟩ := centeredPrimeWeight_periodic_iter 6
  obtain ⟨B,hB,hbound⟩ := sum_fwdDiff_eight_dyadicSpline_le
  refine ⟨A*B,mul_nonneg hA hB,fun {h} hh hsmall b hlarge => ?_⟩
  let x := fun j : ℕ => dyadicSpline (j*h) - dyadicSpline ((j+1:ℕ)*h)
  have h7 (j : ℕ) (hj : j < 7) : x j = 0 := by
    have hl := mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt hj) : (j:ℝ) ≤ 7) hh.le
    have hu := mul_le_mul_of_nonneg_right (by exact_mod_cast hj : ((j+1:ℕ):ℝ) ≤ 7) hh.le
    simp only [x,dyadicSpline_eq_zero_outside (fun hz => (hl.trans_lt hsmall).not_ge hz.1),
      dyadicSpline_eq_zero_outside (fun hz => (hu.trans_lt hsmall).not_ge hz.1),sub_self]
  have htop (j : ℕ) (hj : b ≤ j) : x j = 0 := by
    have hl := hlarge.trans_le (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hh.le)
    have hu := hl.trans_le (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_succ j)) hh.le)
    simp only [x,dyadicSpline_eq_zero_outside (fun hz => hl.not_ge hz.2),
      dyadicSpline_eq_zero_outside (fun hz => hu.not_ge hz.2),sub_self]
  have h1 : h ≤ 1 := by linarith only [hsmall,Real.exp_le_one_iff.mpr (by norm_num : (-8:ℝ) ≤ 0),hh]
  apply (ha x b h7 htop).trans
  have he (j : ℕ) : |GaloisForLFunctions.BezoutValuationIncidence.bdiff^[7] x j| =
      |(fwdDiff h)^[8] dyadicSpline (j*h)| := abs_bdiff_iter_step_eq 7 dyadicSpline h j
  rw [sum_congr rfl (fun j _ => he j),mul_assoc]
  exact mul_le_mul_of_nonneg_left (hbound hh h1 b) hA

private def weightedMesh (g : ℝ → ℝ) (b : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ range b, (g (j*h) - g ((j+1:ℕ)*h))*centeredPrimeWeight 1 j

/-- The sum of absolute increments on any positive mesh is bounded by the
total variation, uniformly in its step and its terminating index. -/
private theorem mesh_variation_bound {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (b : ℕ) {h : ℝ}, 0 < h → |weightedMesh g b h| ≤ A := by
  obtain ⟨F,hF,hW⟩ := centeredPrimeWeight_uniform
  have hW1 : ∀ j, |centeredPrimeWeight 1 j| ≤ F := by simpa only [Nat.cast_one,mul_one] using hW (R := 1) le_rfl
  have hcont := hg.continuous_deriv_one
  have hint : Integrable (fun x => ‖deriv g x‖) :=
    (hcont.integrable_of_hasCompactSupport hs.deriv).norm
  refine ⟨(∫ x : ℝ, ‖deriv g x‖)*F, mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hF,
    fun b h hh => ?_⟩
  let u : ℕ → ℝ := fun j => j*h
  have hmono : Monotone u := fun i j hij => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hh.le
  have hcell (j : ℕ) : |g (u j) - g (u (j+1))| ≤ ∫ x in u j..u (j+1), ‖deriv g x‖ := by
    rw [abs_sub_comm, ←intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hg.differentiable one_ne_zero).differentiableAt (x := x)) (hcont.intervalIntegrable _ _)]
    exact intervalIntegral.norm_integral_le_integral_norm (f := deriv g) (μ := volume) (hmono (Nat.le_succ j))
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ j ∈ range b, (∫ x in u j..u (j+1), ‖deriv g x‖)*F := by
           apply sum_le_sum
           intro j _
           rw [abs_mul]
           exact mul_le_mul (hcell j) (hW1 j) (abs_nonneg _) (intervalIntegral.integral_nonneg
             (hmono (Nat.le_succ _)) fun _ _ => norm_nonneg _)
       _ ≤ _ := by
           rw [←sum_mul, intervalIntegral.sum_integral_adjacent_intervals
             (fun j _ => hcont.norm.intervalIntegrable (u j) (u (j+1))),intervalIntegral.integral_of_le (hmono (Nat.zero_le b))]
           exact mul_le_mul_of_nonneg_right (setIntegral_le_integral hint (Filter.Eventually.of_forall
             (fun _ => norm_nonneg _))) hF

private def conductorDerivativeProfile (u : ℝ) :=
  dyadicSpline u - 2*u*deriv dyadicSpline u

private theorem conductorDerivativeProfile_regular :
    ContDiff ℝ 1 conductorDerivativeProfile ∧ HasCompactSupport conductorDerivativeProfile := by
  have hs : HasCompactSupport dyadicSpline := HasCompactSupport.intro isCompact_Icc
    fun u hu => dyadicSpline_eq_zero_outside hu
  have hder : ContDiff ℝ 1 (deriv dyadicSpline) :=
    (contDiff_six_dyadicSpline.of_le (by norm_num) : ContDiff ℝ (1+1) dyadicSpline).deriv'
  refine ⟨(contDiff_six_dyadicSpline.of_le (by norm_num)).sub
    ((contDiff_const.mul contDiff_id).mul hder), ?_⟩
  exact hs.sub (HasCompactSupport.mul_left hs.deriv)

/-- The size and first conductor derivative are bounded independently of how
many quotient cells lie in the window. -/
theorem real_conductor_mesh_sampling :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℕ) {q x : ℝ}, 0 < q → 0 < x →
      |x*quotientMeshProfile b (q/x^2)| ≤ C*x ∧
      ∃ d : ℝ, |d| ≤ C ∧ HasDerivAt (fun y : ℝ => y*quotientMeshProfile b (q/y^2)) d x := by
  have hs : HasCompactSupport dyadicSpline := HasCompactSupport.intro isCompact_Icc
    fun u hu => dyadicSpline_eq_zero_outside hu
  obtain ⟨A,hA,ha⟩ := mesh_variation_bound (contDiff_six_dyadicSpline.of_le (by norm_num)) hs
  obtain ⟨B,hB,hb⟩ := mesh_variation_bound conductorDerivativeProfile_regular.1 conductorDerivativeProfile_regular.2
  refine ⟨A+B,add_nonneg hA hB,fun b q x hq hx => ?_⟩
  have hh : 0 < q/x^2 := div_pos hq (sq_pos_of_pos hx)
  constructor
  · rw [abs_mul,abs_of_pos hx,mul_comm (A+B)]
    exact mul_le_mul_of_nonneg_left ((ha b hh).trans (le_add_of_nonneg_right hB)) hx.le
  · refine ⟨weightedMesh conductorDerivativeProfile b (q/x^2),
      (hb b hh).trans (le_add_of_nonneg_left hA),?_⟩
    have hd (z : ℝ) : HasDerivAt (fun y : ℝ => y*dyadicSpline (z/y^2))
        (conductorDerivativeProfile (z/x^2)) x := by
      have hq' : HasDerivAt (fun y : ℝ => z/y^2) (-(2*z)/x^3) x := by
        refine ((hasDerivAt_const x z).div ((hasDerivAt_id x).pow 2) (sq_pos_of_pos hx).ne').congr_deriv ?_
        dsimp only [id,Pi.pow_apply]; field_simp; ring
      have hΦ := (contDiff_six_dyadicSpline.differentiable (by simp)).differentiableAt (x := z/x^2)
      refine ((hasDerivAt_id x).mul (hΦ.hasDerivAt.comp x hq')).congr_deriv ?_
      dsimp [conductorDerivativeProfile]; field_simp; ring
    have hd' (j : ℕ) := ((hd ((j:ℝ)*q)).sub (hd (((j+1:ℕ):ℝ)*q))).mul_const (centeredPrimeWeight 1 j)
    have hsum := HasDerivAt.fun_sum (u := range b) fun j _ => hd' j
    simpa only [weightedMesh,quotientMeshProfile,Pi.sub_apply,mul_sum,mul_sub,←mul_div_assoc,←mul_assoc] using hsum

/-- Adjacent products change the mesh by at most a constant divided by the
product. Rescaling the conductor by the square root of their ratio gives
this estimate uniformly even when many quotient boundaries intervene. -/
theorem quotientMeshProfile_product_variation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℕ) {q d : ℝ}, 0 < q → 0 < d →
      |quotientMeshProfile b (q*d)| ≤ C ∧
      |quotientMeshProfile b ((q+1)*d)-quotientMeshProfile b (q*d)| ≤ 2*C/q := by
  obtain ⟨C,hC,h⟩ := real_conductor_mesh_sampling
  refine ⟨C,hC,fun b q d hq hd => ?_⟩
  have size := (h b (mul_pos hq hd) zero_lt_one).1
  simp only [one_pow,div_one,one_mul,mul_one] at size
  refine ⟨size,?_⟩
  let s := (q+1)*d
  let t := Real.sqrt ((q+1)/q)
  let F := fun x : ℝ => x * quotientMeshProfile b (s/x^2)
  have hs : 0 < s := mul_pos (by linarith only [hq]) hd
  have hr : 1 ≤ (q+1)/q := (le_div_iff₀ hq).mpr (by linarith only)
  have ht : 1 ≤ t := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr
  have ht' := zero_lt_one.trans_le ht
  have ht2 : t^2 = (q+1)/q := Real.sq_sqrt (zero_le_one.trans hr)
  have hratio : s/t^2 = q*d := by
    rw [ht2]; dsimp only [s]; field_simp [(by linarith only [hq] : q+1≠0)]
  have hdist : t-1 ≤ 1/q := by
    have hh := le_mul_of_one_le_right ht'.le ht
    rw [←sq,ht2] at hh
    rw [add_div,div_self hq.ne'] at hh
    linarith only [hh]
  have hdiff (x : ℝ) (hx : x ∈ Set.Ioi (0:ℝ)) : DifferentiableAt ℝ F x := by
    obtain ⟨_,_,hx'⟩ := (h b hs hx).2
    exact hx'.differentiableAt
  have hder (x : ℝ) (hx : x ∈ Set.Ioi (0:ℝ)) : ‖deriv F x‖ ≤ C := by
    obtain ⟨_,hx',hD⟩ := (h b hs hx).2
    rwa [show deriv F x = _ from hD.deriv,Real.norm_eq_abs]
  have hlip := (convex_Ioi (0:ℝ)).norm_image_sub_le_of_norm_deriv_le hdiff hder
    (Set.mem_Ioi.mpr ht') (Set.mem_Ioi.mpr (zero_lt_one : (0:ℝ)<1))
  simp only [F,one_pow,div_one,one_mul,hratio,Real.norm_eq_abs,abs_sub_comm 1 t,
    abs_of_nonneg (sub_nonneg.mpr ht)] at hlip
  let v := quotientMeshProfile b (q*d)
  have he : quotientMeshProfile b s-v = (quotientMeshProfile b s-t*v)+(t-1)*v := by ring
  change |quotientMeshProfile b s-v| ≤ _
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr ht)]
  have hm := mul_le_mul_of_nonneg_left size (sub_nonneg.mpr ht)
  have hc := mul_le_mul_of_nonneg_left hdist hC
  change |quotientMeshProfile b s-t*v| ≤ C*(t-1) at hlip
  change (t-1)*|v| ≤ _ at hm
  simp only [div_eq_mul_inv] at hc ⊢
  linarith only [hlip,hm,hc]

/-- Every sharp product interval in the real mesh inherits the ordinary
prime-error exponent. Abel summation keeps the final sample at each cut. -/
theorem quotientMeshProfile_prime_interval {β : ℝ} (hβ : _root_.RHTower.zeroReSup < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b L H : ℕ) {d : ℝ}, 0 < d → L ≤ H →
      |∑ q ∈ Ioc L H, (vonMangoldt q-1)*quotientMeshProfile b (q*d)| ≤ C*(H:ℝ)^β := by
  obtain ⟨A,hA,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow hβ
  obtain ⟨D,hD,hV⟩ := quotientMeshProfile_product_variation
  have hhalf : 1/2 < β := _root_.RHTower.half_le_zeroReSup.trans_lt hβ
  have hpos : 0 < β := (by norm_num : (0:ℝ)<1/2).trans hhalf
  let a (q : ℕ) := vonMangoldt q-1
  have prim (k : ℕ) (hk : 1 ≤ k) : |∑ q ∈ Icc 1 k, a q| ≤ A*(k:ℝ)^β := by
    have hψ' : (∑ q ∈ Icc 1 k, vonMangoldt q) = Chebyshev.psi k := by
      unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
    simp only [a,sum_sub_distrib,hψ',sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
    exact hψ k (by exact_mod_cast hk)
  refine ⟨10*A*D,by positivity,fun b L H d hd hLH => ?_⟩
  let V (k : ℕ) := quotientMeshProfile b (k*d)
  have prefixBound (K : ℕ) : |∑ k ∈ Icc 1 K, a k*V k| ≤ 5*A*D*(K:ℝ)^β := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [Real.zero_rpow hpos.ne']
    have hK' : (0:ℝ) < K := Nat.cast_pos.mpr hK
    have hKpow : (K:ℝ)^(β-1/2)*Real.sqrt K=(K:ℝ)^β := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_add hK',sub_add_cancel]
    have cell (k : ℕ) (hk : k ∈ Icc 1 K) :
        |(∑ q ∈ Icc 1 k, a q)*(V k-V (k+1))| ≤
          (2*A*D*(K:ℝ)^(β-1/2))*(1/Real.sqrt k) := by
      have hk0 := (mem_Icc.mp hk).1
      have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk0
      have hv := (hV b hk' hd).2
      have hv' : |V k-V (k+1)| ≤ 2*D/k := by
        simpa only [V,Nat.cast_add,Nat.cast_one,abs_sub_comm (quotientMeshProfile b (k*d))] using hv
      have hp : (k:ℝ)^β/(k:ℝ)=(k:ℝ)^(β-1/2)/Real.sqrt k := by
        rw [Real.sqrt_eq_rpow,←Real.rpow_sub hk',show β-1/2-1/2=β-1 by ring,Real.rpow_sub_one hk'.ne']
      have hscale := Real.rpow_le_rpow hk'.le (Nat.cast_le.mpr (mem_Icc.mp hk).2) (sub_nonneg.mpr hhalf.le)
      rw [abs_mul]
      apply (mul_le_mul (prim k hk0) hv' (abs_nonneg _) (mul_nonneg hA (Real.rpow_nonneg hk'.le _))).trans
      calc (A*(k:ℝ)^β)*(2*D/k) = (2*A*D)*((k:ℝ)^β/k) := by ring
           _ ≤ _ := by
             rw [hp]
             exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hscale (Real.sqrt_nonneg _))
               (by positivity : 0 ≤ 2*A*D)).trans_eq (by ring)
    rw [_root_.HTGeometry.sum_mul_eq_partial_mul_diff_ring a V]
    have hsum := ((abs_sum_le_sum_abs _ _).trans (sum_le_sum cell)).trans_eq
      (mul_sum (s := Icc 1 K) (f := fun k : ℕ => 1/Real.sqrt k) _).symm
    have hs := hsum.trans (mul_le_mul_of_nonneg_left (_root_.RHTower.sum_inv_sqrt_le K) (by positivity))
    have hv := (hV b (Nat.cast_pos.mpr (Nat.succ_pos K)) hd).1
    have hend := mul_le_mul (prim K hK) hv (abs_nonneg _) (mul_nonneg hA (Real.rpow_nonneg hK'.le β))
    rw [←abs_mul] at hend
    apply (abs_add_le _ _).trans ((add_le_add hs hend).trans_eq ?_)
    linear_combination 4*A*D*hKpow
  have hi (k : ℕ) : Ioc 0 k = Icc 1 k := by ext q; simp only [mem_Ioc,mem_Icc]; omega
  have hs := sum_Ioc_consecutive (fun q : ℕ => a q*V q) (Nat.zero_le L) hLH
  rw [hi,hi] at hs
  change |∑ q ∈ Ioc L H, a q*V q| ≤ _
  rw [show (∑ q ∈ Ioc L H, a q*V q) = (∑ q ∈ Icc 1 H, a q*V q)-(∑ q ∈ Icc 1 L, a q*V q)
    by linarith only [hs]]
  have hL := (prefixBound L).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hLH) hpos.le) (by positivity))
  exact (abs_sub _ _).trans ((add_le_add (prefixBound H) hL).trans_eq (by ring))

/-- Replacing integer conductors by their integral costs one constant per
unit interval, uniformly in both the product and the quotient cutoff. -/
theorem conductor_mesh_integral_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a d : ℕ}, 0 < a → a ≤ d → ∀ (b : ℕ) {q : ℝ}, 0 < q →
      |(∑ n ∈ Ico a d, (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2)) -
        ∫ x in (a:ℝ)..d, x*quotientMeshProfile b (q/x^2)| ≤ C*(d-a : ℕ) := by
  obtain ⟨C,hC,h⟩ := real_conductor_mesh_sampling
  refine ⟨C,hC,fun {a d} ha had b q hq => ?_⟩
  let F := fun x : ℝ => x * quotientMeshProfile b (q/x^2)
  have hdif (x : ℝ) (hx : x ∈ Set.Ioi (0:ℝ)) : DifferentiableAt ℝ F x := by
    obtain ⟨_,_,hd⟩ := (h b hq hx).2
    exact hd.differentiableAt
  have hder (x : ℝ) (hx : x ∈ Set.Ioi (0:ℝ)) : ‖deriv F x‖ ≤ C := by
    obtain ⟨_,hb,hd⟩ := (h b hq hx).2
    rwa [show deriv F x = _ from hd.deriv,Real.norm_eq_abs]
  have hint (n : ℕ) (hn : n ∈ Ico a d) : IntervalIntegrable F volume (n:ℝ) ((n+1:ℕ):ℝ) := by
    apply ContinuousOn.intervalIntegrable
    have hnn : (n:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.le_succ n
    rw [Set.uIcc_of_le hnn]
    intro x hx
    exact (hdif x ((Nat.cast_pos.mpr (ha.trans_le (mem_Ico.mp hn).1)).trans_le hx.1)).continuousAt.continuousWithinAt
  have hcell (n : ℕ) (hn : n ∈ Ico a d) :
      |F n - ∫ x in (n:ℝ)..((n+1:ℕ):ℝ), F x| ≤ C := by
    have hn' : (0:ℝ) < n := Nat.cast_pos.mpr (ha.trans_le (mem_Ico.mp hn).1)
    have hnn : (n:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.le_succ n
    have hpt (x : ℝ) (hx : x ∈ Set.uIoc (n:ℝ) ((n+1:ℕ):ℝ)) : ‖F n - F x‖ ≤ C := by
      rw [Set.uIoc_of_le hnn] at hx
      have hh := (convex_Ioi (0:ℝ)).norm_image_sub_le_of_norm_deriv_le hdif hder
        (hn'.trans hx.1) hn'
      have hdist : ‖(n:ℝ)-x‖ ≤ 1 := by
        rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
        have hu := hx.2
        push_cast at hu
        linarith
      exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdist hC)
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint n hn),
      intervalIntegral.integral_const,smul_eq_mul,Real.norm_eq_abs] at hh
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,one_mul,abs_one,mul_one] using hh
  change |(∑ n ∈ Ico a d, F n) - ∫ x in (a:ℝ)..d, F x| ≤ _
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k : ℕ => (k:ℝ))
    had (fun k hk => hint k (mem_Ico.mpr hk)),←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _n ∈ Ico a d, C := sum_le_sum hcell
       _ = _ := by rw [sum_const,Nat.card_Ico,nsmul_eq_mul,mul_comm]

/-- At a fixed rescaled conductor all retained products have precisely the
same spline mesh. The factor q is the product of the conductor weight and Jacobian. -/
theorem rescaled_mesh_density (b : ℕ) {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    (t*Real.sqrt q * quotientMeshProfile b (q/(t*Real.sqrt q)^2))*Real.sqrt q =
      t*quotientMeshProfile b (1/t^2)*q := by
  have hs := Real.sq_sqrt hq.le
  have hdiv : q/(t*Real.sqrt q)^2 = 1/t^2 := by rw [mul_pow,hs]; field_simp
  rw [hdiv]
  linear_combination (t*quotientMeshProfile b (1/t^2))*hs

private theorem continuous_quotientMeshProfile (b : ℕ) : Continuous (quotientMeshProfile b) := by
  have hf := contDiff_six_dyadicSpline.continuous
  unfold quotientMeshProfile
  fun_prop

/-- Scaling each conductor integral by its own square root and then exchanging
the finite product sum places the prime coefficients in one common interval.
The four inequalities keep the two conductor and two product boundaries. -/
theorem rescaled_shell_integral_exchange (b Q H : ℕ) (L U c α β : ℝ)
    {T Z : ℝ} (hT : 0 < T) (hTZ : T ≤ Z) :
    (∑ q ∈ Ioc Q H, ∫ x in T*Real.sqrt q..Z*Real.sqrt q,
      if L < x ∧ x ≤ U ∧ x^α < (q:ℝ) ∧ (q:ℝ) ≤ c*x^β then
        (vonMangoldt q-1) * (x*quotientMeshProfile b (q/x^2)) else 0) =
      ∫ t in T..Z, (t*quotientMeshProfile b (1/t^2)) *
        ∑ q ∈ rescaledShellProducts H L U t α β c with Q < q, (vonMangoldt q-1)*q := by
  classical
  let S := Ioc Q H
  let keep (q : ℕ) (t : ℝ) : Prop := L < t*Real.sqrt q ∧ t*Real.sqrt q ≤ U ∧
    (t*Real.sqrt q)^α < (q:ℝ) ∧ (q:ℝ) ≤ c*(t*Real.sqrt q)^β
  let B := fun t : ℝ => t*quotientMeshProfile b (1/t^2)
  let F := fun (q : ℕ) (t : ℝ) => if keep q t then B t*((vonMangoldt q-1)*q) else 0
  have mask (t : ℝ) : S.filter (fun q => keep q t) =
      (rescaledShellProducts H L U t α β c).filter (Q < ·) := by
    ext q
    simp only [S,keep,rescaledShellProducts,mem_filter,mem_Ioc,mem_Icc]
    constructor
    · rintro ⟨⟨hlo,hu⟩,hk⟩
      exact ⟨⟨⟨(Nat.zero_le Q).trans_lt hlo,hu⟩,hk⟩,hlo⟩
    · rintro ⟨⟨⟨_,hu⟩,hk⟩,hlo⟩
      exact ⟨⟨hlo,hu⟩,hk⟩
  have hb : ContinuousOn B (Set.Icc T Z) := by
    intro t ht
    have ht0 := hT.trans_le ht.1
    exact (continuousAt_id.mul ((continuous_quotientMeshProfile b).continuousAt.comp
      (continuousAt_const.div (continuousAt_id.pow 2) (sq_pos_of_pos ht0).ne'))).continuousWithinAt
  have hint (q : ℕ) (_ : q ∈ S) : IntervalIntegrable (F q) volume T Z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTZ]
    have hbase : IntervalIntegrable (fun t => B t*((vonMangoldt q-1)*q)) volume T Z :=
      (hb.mul continuousOn_const).intervalIntegrable_of_Icc hTZ
    have hm : MeasurableSet {t | keep q t} := by
      have hx : Measurable (fun t : ℝ => t*Real.sqrt q) := measurable_id.mul_const _
      have hlo : Measurable (fun t : ℝ => (t*Real.sqrt q)^α) := by fun_prop
      have hhi : Measurable (fun t : ℝ => c*(t*Real.sqrt q)^β) := by fun_prop
      exact (measurableSet_lt (g := fun t : ℝ => t*Real.sqrt q) (f := fun _ => L) measurable_const hx).inter
        ((measurableSet_le hx (measurable_const (a := U))).inter
          ((measurableSet_lt hlo (measurable_const (a := (q:ℝ)))).inter
            (measurableSet_le (measurable_const (a := (q:ℝ))) hhi)))
    have heq : F q = {t | keep q t}.indicator (fun t => B t*((vonMangoldt q-1)*q)) := by
      funext t
      by_cases ht : keep q t
      · rw [Set.indicator_of_mem (show t ∈ {y | keep q y} from ht)]
        exact if_pos ht
      · rw [Set.indicator_of_notMem (show t ∉ {y | keep q y} from ht)]
        exact if_neg ht
    rw [heq]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hTZ).mp hbase).indicator hm
  calc _ = ∑ q ∈ S, ∫ t in T..Z, F q t := by
            apply sum_congr rfl
            intro q hq
            let G := fun x : ℝ => if L < x ∧ x ≤ U ∧ x^α < (q:ℝ) ∧ (q:ℝ) ≤ c*x^β then
              (vonMangoldt q-1)*(x*quotientMeshProfile b (q/x^2)) else 0
            change (∫ x in T*Real.sqrt q..Z*Real.sqrt q, G x) = _
            rw [← intervalIntegral.smul_integral_comp_mul_right G (Real.sqrt q), smul_eq_mul,
              ←intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro t ht
            rw [Set.uIcc_of_le hTZ] at ht
            have hq0 : (0:ℝ) < q := Nat.cast_pos.mpr ((Nat.zero_le Q).trans_lt (mem_Ioc.mp hq).1)
            change Real.sqrt q*(if keep q t then _ else 0) = if keep q t then _ else 0
            by_cases hk : keep q t
            · rw [if_pos hk,if_pos hk]
              dsimp only [B]
              linear_combination (vonMangoldt q-1)*rescaled_mesh_density b hq0 (hT.trans_le ht.1)
            · rw [if_neg hk,if_neg hk,mul_zero]
       _ = ∫ t in T..Z, ∑ q ∈ S, F q t := (intervalIntegral.integral_finsetSum hint).symm
       _ = _ := by
            apply intervalIntegral.integral_congr
            intro t _
            dsimp only [F]
            rw [←sum_filter,mask,←mul_sum]

/-- The mesh supplies the integrable density t⁻¹³, so the bound is uniform
in the upper endpoint, even across many product scales. -/
theorem rescaled_shell_integral_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H b : ℕ, 1 ≤ H → ∀ Q ≤ H, ∀ L U c : ℝ, ∀ {α β T Z : ℝ},
      α ≤ 2 → β ≤ 2 → 0 < T → T ≤ Z →
      7/T^2 < Real.exp (-8) → 4*Real.exp 8 < b/Z^2 →
      |∫ t in T..Z, (t*quotientMeshProfile b (1/t^2)) *
        ∑ q ∈ rescaledShellProducts H L U t α β c with Q < q, (vonMangoldt q-1)*q| ≤
        C*(H:ℝ)^(1+(8/9:ℝ))/T^12 := by
  obtain ⟨A,hA,ha⟩ := quotientMeshProfile_seventh
  obtain ⟨P,hP,hp⟩ := rescaledShellProducts_band_mass
  refine ⟨A*P/12,by positivity,fun H b hH Q hQ L U c α β T Z hα hβ hT hTZ hsmall hlarge => ?_⟩
  let B := A*P*(H:ℝ)^(1+(8/9:ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpnt (t : ℝ) (ht : t ∈ Set.Ioc T Z) :
      ‖(t*quotientMeshProfile b (1/t^2)) * ∑ q ∈ rescaledShellProducts H L U t α β c with Q < q,
        (vonMangoldt q-1)*q‖ ≤ B*(t^13)⁻¹ := by
    have ht0 := hT.trans ht.1
    have hst : 7*(1/t^2) < Real.exp (-8) := by
      rw [←div_eq_mul_one_div]
      exact (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hT)
        (pow_le_pow_left₀ hT.le ht.1.le 2)).trans_lt hsmall
    have hbt : 4*Real.exp 8 < (b:ℝ)*(1/t^2) := by
      rw [←div_eq_mul_one_div]
      exact hlarge.trans_le (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sq_pos_of_pos ht0)
        (pow_le_pow_left₀ ht0.le ht.2 2))
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos ht0]
    have hm := ha (one_div_pos.mpr (sq_pos_of_pos ht0)) hst b hbt
    have he : t*(A*(1/t^2)^7) = A/t^13 := by field_simp
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hm ht0.le) (hp H hH Q hQ L U c ht0.le hα hβ)
      (abs_nonneg _) (by positivity)).trans
    rw [he]
    exact le_of_eq (by dsimp only [B]; ring)
  have hzero : (0:ℝ) ∉ Set.uIcc T Z := by
    rw [Set.uIcc_of_le hTZ]
    exact fun h => hT.not_ge h.1
  have hint : IntervalIntegrable (fun t : ℝ => B*(t^13)⁻¹) volume T Z := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_const.mul ((continuousOn_id.pow 13).inv₀ ?_)
    exact fun t ht => pow_ne_zero _ (fun h => hzero (h ▸ ht))
  have h := intervalIntegral.norm_integral_le_of_norm_le hTZ (Filter.Eventually.of_forall hpnt) hint
  rw [Real.norm_eq_abs,intervalIntegral.integral_const_mul] at h
  have hi : (∫ x : ℝ in T..Z, (x^13)⁻¹) = ((Z^12)⁻¹-(T^12)⁻¹)/(-12) := by
    calc _ = ∫ x : ℝ in T..Z, x^(-13:ℤ) := by
             apply intervalIntegral.integral_congr
             exact fun x _ => (zpow_negSucc x 12).symm
         _ = _ := by
             rw [integral_zpow (Or.inr ⟨by norm_num,hzero⟩),show (-13:ℤ)+1=-12 by norm_num]
             have hp (x : ℝ) : x^(-12:ℤ)=(x^12)⁻¹ := zpow_negSucc x 11
             rw [hp,hp]
             norm_num
  rw [hi] at h
  have hdrop := mul_nonneg hB (inv_nonneg.mpr (pow_nonneg (hT.trans_le hTZ).le 12))
  dsimp only [B] at h hdrop
  simp only [div_eq_mul_inv] at h ⊢
  linarith only [h,hdrop]

#print axioms conductor_mesh_integral_error
#print axioms quotientMeshProfile_product_variation
#print axioms quotientMeshProfile_prime_interval
#print axioms quotientMeshProfile_seventh
#print axioms rescaled_shell_integral_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
