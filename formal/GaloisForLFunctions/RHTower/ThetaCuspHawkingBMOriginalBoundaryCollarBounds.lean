import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCompleteTransfer

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalBoundaryCollarBounds
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMOriginalCompleteTransfer
open D4BMOriginalAngularProducts D4BMOriginalForcingProductBounds
noncomputable section
set_option autoImplicit false

/-- The actual leading horizon trace of every transfer, with the same reader
and original source principal subtraction as the finite collar. -/
def horizonTransfer (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 4)
    (p x k : ℝ) : ℂ :=
  Complex.exp (-w*(p:ℂ))*
    ![horizonAngularProduct q br amp w 0 true p x k,
      Complex.exp (-(k:ℂ))*horizonAngularProduct q br amp w 1 false p x k,
      Complex.exp (2*(k:ℂ))*horizonAngularProduct q br amp w 2 true p x k+
        horizonAngularProduct q br amp w 3 true p x k-horizonAngularProduct q br amp w 1 true p x k,
      horizonProduct q br amp w true p x k] j

/-- All four original metric transfers share a time/radial-integrable cusp
error envelope after the actual radial Jacobian. No relative cutoff rate is imposed. -/
theorem radial_transfer_error (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ C : ℝ,0≤C ∧ ∀ᶠ L : ℝ in atTop,∀ p x k : ℝ,0<p → 0≤k → ∀ j : Fin 4,
        ‖radialTransfer q br amp w j p L x k-horizonTransfer q br amp w j p x k‖≤
          C*Real.exp (-L)*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  classical
  choose G hG hg using (fun (j : Fin 5) (d : Bool) => original_angular_product_error q br amp j d (N+2))
  let H := ∑ j : Fin 5,∑ d : Bool,G j d
  have hH : 0≤H := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hG j d))
  have hjH (j : Fin 5) (d : Bool) : G j d≤H := by
    exact (Finset.single_le_sum (fun e _ => hG j e) (Finset.mem_univ d)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun e _ => hG l e)) (Finset.mem_univ j))
  refine ⟨H,hH,?_⟩
  intro w hwi hw
  have hw1 : 1≤w.re := by linarith
  choose B hB hb using (fun (j : Fin 5) (d : Bool) => hg j d w hwi (by linarith [hjH j d]))
  obtain ⟨D,hD,hd⟩ := original_forcing_product_error q br amp w true (N+2) hwi hw1
  let M := (∑ j : Fin 5,∑ d : Bool,B j d)+D
  have hM : 0≤M := add_nonneg (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hB j d))) hD
  have hjM (j : Fin 5) (d : Bool) : B j d≤M := by
    have h := (Finset.single_le_sum (fun e _ => hB j e) (Finset.mem_univ d)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun e _ => hB l e)) (Finset.mem_univ j))
    exact h.trans (le_add_of_nonneg_right hD)
  have hDM : D≤M := le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hB j d)))
  have hall : ∀ᶠ L : ℝ in atTop,∀ j : Fin 5,∀ d : Bool,∀ p x k : ℝ,0<p → 0≤k →
      ‖Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w j d p L x k-horizonAngularProduct q br amp w j d p x k)‖≤
        B j d*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-((N+2:ℕ):ℝ)*k)*Real.exp (-p) := by
    exact Filter.eventually_all.mpr (fun j => Filter.eventually_all.mpr (hb j))
  refine ⟨6*M,by positivity,?_⟩
  filter_upwards [hall,hd,eventually_gt_atTop (0:ℝ)] with L hs hf hL p x k hp hk j
  let E := (2*M)*Real.exp (-L)*Real.exp (-(N:ℝ)*k)*Real.exp (-p)
  have hE : 0≤E := by dsimp [E];positivity
  have hS : Real.exp (-L)+Real.exp (-w.re*L)≤2*Real.exp (-L) := by
    have h : Real.exp (-w.re*L)≤Real.exp (-L) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hNk : Real.exp (-((N+2:ℕ):ℝ)*k)≤Real.exp (-(N:ℝ)*k) := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have h2k : Real.exp (2*k)*Real.exp (-((N+2:ℕ):ℝ)*k)=Real.exp (-(N:ℝ)*k) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hc (l : Fin 5) (d : Bool) :
      ‖Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w l d p L x k-horizonAngularProduct q br amp w l d p x k)‖≤E := by
    apply (hs l d p x k hp hk).trans
    change _≤(2*M)*Real.exp (-L)*Real.exp (-(N:ℝ)*k)*Real.exp (-p)
    calc
      _ ≤ M*(2*Real.exp (-L))*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
        gcongr
        exact hjM l d
      _ = _ := by ring
  have hc2 : ‖Complex.exp (2*(k:ℂ))*(Complex.exp (-w*(p:ℂ))*
      (angularProduct q br amp w 2 true p L x k-horizonAngularProduct q br amp w 2 true p x k))‖≤E := by
    have hn : ‖Complex.exp (2*(k:ℂ))‖=Real.exp (2*k) := by simp [Complex.norm_exp]
    rw [norm_mul,hn]
    calc
      _ ≤ Real.exp (2*k)*(M*(2*Real.exp (-L))*Real.exp (-((N+2:ℕ):ℝ)*k)*Real.exp (-p)) := by
        gcongr
        exact (hs 2 true p x k hp hk).trans (by gcongr; exact hjM 2 true)
      _ = E := by dsimp [E]; rw [show Real.exp (2*k)*(M*(2*Real.exp (-L))*Real.exp (-((N+2:ℕ):ℝ)*k)*Real.exp (-p))=
          (2*M)*Real.exp (-L)*(Real.exp (2*k)*Real.exp (-((N+2:ℕ):ℝ)*k))*Real.exp (-p) by ring,h2k]
  have hc1 : ‖Complex.exp (-(k:ℂ))*(Complex.exp (-w*(p:ℂ))*
      (angularProduct q br amp w 1 false p L x k-horizonAngularProduct q br amp w 1 false p x k))‖≤E := by
    have he : ‖Complex.exp (-(k:ℂ))‖≤1 := by
      rw [Complex.norm_exp]
      simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hk)
    rw [norm_mul]
    exact (mul_le_mul he (hc 1 false) (norm_nonneg _) (by norm_num)).trans_eq (one_mul E)
  have hcf : ‖Complex.exp (-w*(p:ℂ))*(normalizedProduct q br amp w true p L x k-horizonProduct q br amp w true p x k)‖≤E := by
    apply (hf p x k hp hk).trans
    calc
      _ ≤ M*(2*Real.exp (-L))*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by gcongr
      _ = E := by dsimp [E];ring
  have hgoal : 3*E=(6*M)*Real.exp (-L)*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by dsimp [E];ring
  rw [← hgoal]
  fin_cases j
  · change ‖radialTransfer q br amp w 0 p L x k-horizonTransfer q br amp w 0 p x k‖≤_
    simpa [radialTransfer,normalizedTransfer,horizonTransfer,← mul_sub] using (hc 0 true).trans (by nlinarith : E≤3*E)
  · change ‖radialTransfer q br amp w 1 p L x k-horizonTransfer q br amp w 1 p x k‖≤_
    have he : radialTransfer q br amp w 1 p L x k-horizonTransfer q br amp w 1 p x k=
      Complex.exp (-(k:ℂ))*(Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w 1 false p L x k-horizonAngularProduct q br amp w 1 false p x k)) := by
      simp [radialTransfer,normalizedTransfer,horizonTransfer]
      ring
    rw [he]
    exact hc1.trans (by nlinarith)
  · change ‖radialTransfer q br amp w 2 p L x k-horizonTransfer q br amp w 2 p x k‖≤_
    have he : radialTransfer q br amp w 2 p L x k-horizonTransfer q br amp w 2 p x k=
      Complex.exp (2*(k:ℂ))*(Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w 2 true p L x k-horizonAngularProduct q br amp w 2 true p x k))+
      Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w 3 true p L x k-horizonAngularProduct q br amp w 3 true p x k)-
      Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w 1 true p L x k-horizonAngularProduct q br amp w 1 true p x k) := by
      simp [radialTransfer,normalizedTransfer,horizonTransfer]
      ring
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      ((add_le_add (add_le_add hc2 (hc 3 true)) (hc 1 true)).trans_eq (by ring)))
  · change ‖radialTransfer q br amp w 3 p L x k-horizonTransfer q br amp w 3 p x k‖≤_
    simpa [radialTransfer,horizonTransfer,← mul_sub] using hcf.trans (by nlinarith : E≤3*E)

private theorem exponential_interval_bound (f : ℝ→ℂ) (C a b : ℝ) (hC : 0≤C) (hab : a≤b)
    (h : ∀ p∈Ioc a b,‖f p‖≤C*Real.exp (-p)) :
    ‖∫ p in a..b,f p‖≤C*Real.exp (-a) := by
  have hi : IntervalIntegrable (fun p : ℝ => C*Real.exp (-p)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall h) hi
  calc
    _ ≤ ∫ p in a..b,C*Real.exp (-p) := hb
    _ = C*(Real.exp (-a)-Real.exp (-b)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp]
    _ ≤ C*Real.exp (-a) := by nlinarith [Real.exp_nonneg (-b)]

/-- The complete physical boundary functional with its actual leading horizon
trace subtracted inside each transfer. Both original time endpoint values remain. -/
def boundaryError (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  let mu := D4BMLeftModeRadialEquation.eigenvalue q
  let F := fun j p => ∫ x in (-1/2:ℝ)..1/2,
    radialTransfer q br amp w j p L x k-horizonTransfer q br amp w j p x k
  (-(mu-2)*(F 0 b-F 0 a)+w*(mu*(∫ p in a..b,F 1 p)-(∫ p in a..b,F 2 p)-
    2*(mu-2)*(∫ p in a..b,F 0 p)-(∫ p in a..b,F 3 p)))

/-- The combined source/forcing boundary and both endpoint corrections have
an integrable horizon envelope uniform over every positive time interval. -/
theorem complete_boundary_error_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ C : ℝ,0≤C ∧ ∀ᶠ L : ℝ in atTop,∀ a b k : ℝ,0<a → a≤b → 0≤k →
        ‖boundaryError q br amp w a b L k‖≤C*Real.exp (-L)*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := radial_transfer_error q br amp N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := hg w hwi hw
  let mu := D4BMLeftModeRadialEquation.eigenvalue q
  let lam := mu-2
  let B := 2*‖lam‖*C+‖w‖*(‖mu‖+2+2*‖lam‖)*C
  have hB : 0≤B := by dsimp [B];positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [hc] with L hL a b k ha hab hk
  let A := C*Real.exp (-L)*Real.exp (-(N:ℝ)*k)
  have hA : 0≤A := by dsimp [A];positivity
  let F := fun j p => ∫ x in (-1/2:ℝ)..1/2,
    radialTransfer q br amp w j p L x k-horizonTransfer q br amp w j p x k
  have hF (j : Fin 4) (p : ℝ) (hp : 0<p) : ‖F j p‖≤A*Real.exp (-p) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun x _ => hL p x k hp hk j)
    simpa only [F,A,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one,neg_div] using h
  have hF' (j : Fin 4) (p : ℝ) (hp : 0<p) : ‖F j p‖≤A := by
    exact (hF j p hp).trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith : -p≤0)) hA).trans_eq (mul_one A))
  have hI (j : Fin 4) : ‖∫ p in a..b,F j p‖≤A := by
    have h := exponential_interval_bound (F j) A a b hA hab
      (fun p hp => hF j p (ha.trans hp.1))
    exact h.trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith : -a≤0)) hA).trans_eq (mul_one A))
  change ‖-lam*(F 0 b-F 0 a)+w*(mu*(∫ p in a..b,F 1 p)-(∫ p in a..b,F 2 p)-
    2*lam*(∫ p in a..b,F 0 p)-(∫ p in a..b,F 3 p))‖≤_
  calc
    _ ≤ ‖lam‖*(‖F 0 b‖+‖F 0 a‖)+‖w‖*
        ((‖mu‖*‖∫ p in a..b,F 1 p‖+‖∫ p in a..b,F 2 p‖)+
          2*‖lam‖*‖∫ p in a..b,F 0 p‖+‖∫ p in a..b,F 3 p‖) := by
      apply (norm_add_le _ _).trans
      simp only [norm_mul,norm_neg]
      gcongr
      · exact norm_sub_le _ _
      · have h := (norm_sub_le
          (mu*(∫ p in a..b,F 1 p)-(∫ p in a..b,F 2 p)-2*lam*(∫ p in a..b,F 0 p))
          (∫ p in a..b,F 3 p)).trans (add_le_add
          ((norm_sub_le (mu*(∫ p in a..b,F 1 p)-(∫ p in a..b,F 2 p))
            (2*lam*(∫ p in a..b,F 0 p))).trans (add_le_add
              (norm_sub_le (mu*(∫ p in a..b,F 1 p)) (∫ p in a..b,F 2 p)) le_rfl)) le_rfl)
        simpa only [norm_mul,Complex.norm_ofNat] using h
    _ ≤ ‖lam‖*(A+A)+‖w‖*((‖mu‖*A+A)+2*‖lam‖*A+A) := by
      gcongr
      · exact hF' 0 b (ha.trans_le hab)
      · exact hF' 0 a ha
      all_goals exact hI _
    _ = B*Real.exp (-L)*Real.exp (-(N:ℝ)*k) := by dsimp [B,A];ring

/-- Arbitrary radial and temporal cutoffs retain the same cusp error bound
after integration over the original horizon collar. -/
theorem complete_boundary_collar_error_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ C L0 : ℝ,0≤C ∧ 0<L0 ∧ ∀ a b M k : ℝ,0<a → a≤b → L0≤M → 0≤k →
        ‖∫ L in L0..M,boundaryError q br amp w a b L k‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := complete_boundary_error_bound q br amp N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := hg w hwi hw
  obtain ⟨L1,hL1⟩ := eventually_atTop.mp hc
  let L0 := max L1 1
  have hL0 : 0<L0 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  refine ⟨C,L0,hC,hL0,?_⟩
  intro a b M k ha hab hM hk
  have h := exponential_interval_bound (fun L => boundaryError q br amp w a b L k)
    (C*Real.exp (-(N:ℝ)*k)) L0 M (by positivity) hM (by
      intro L hL
      have h' := hL1 L ((le_max_left L1 1).trans hL.1.le) a b k ha hab hk
      simpa only [mul_right_comm] using h')
  exact h.trans ((mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (by linarith : -L0≤0)) (by positivity)).trans_eq (mul_one _))

/-- Independent cutoff removal for the complete horizon-subtracted metric
boundary, uniformly over arbitrary positive temporal intervals and radial cutoffs. -/
theorem complete_boundary_collar_joint_limit (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ L0 : ℝ,0<L0 ∧
      ∀ (T : ℝ×ℝ→{v : ℝ×ℝ // 0<v.1 ∧ v.1≤v.2}) (M : ℝ×ℝ→Ici L0),
        Tendsto (fun z : ℝ×ℝ => ∫ L in L0..(M z:ℝ),
          boundaryError q br amp w (T z).val.1 (T z).val.2 L z.2)
          ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨G,hG,hg⟩ := complete_boundary_collar_error_bound q br amp 1
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨C,L0,hC,hL0,h⟩ := hg w hwi hw
  refine ⟨L0,hL0,?_⟩
  intro T M
  have he : Tendsto (fun z : ℝ×ℝ => C*Real.exp (-z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).comp tendsto_snd
  apply squeeze_zero_norm' _ he
  filter_upwards [((eventually_ge_atTop (0:ℝ)).prod_mk (eventually_ge_atTop (0:ℝ)))] with z hz
  simpa only [Nat.cast_one,neg_one_mul] using
    h (T z).val.1 (T z).val.2 (M z) z.2 (T z).property.1 (T z).property.2 (M z).property hz.2

end
end RHTower.D4BMOriginalBoundaryCollarBounds
