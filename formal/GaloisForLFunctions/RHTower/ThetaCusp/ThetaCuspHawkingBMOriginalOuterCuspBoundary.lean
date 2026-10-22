import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalOuterCuspProducts
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalStaticMetricCollar

/-! All four actual boundary transfers on the finite outer interval. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalOuterCuspBoundary
open D4BMJointSource D4BMModularCore D4BMOriginalOuterCuspProducts
open D4BMOriginalAngularProducts D4BMOriginalForcingProductBounds D4BMOriginalCompleteTransfer
open D4BMOriginalSourceRadialRestoration D4BMOriginalStaticMetricCollar
noncomputable section
set_option autoImplicit false

theorem outer_transfer_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∀ A : ℝ,0<A → ∃ C : ℝ,0≤C ∧
      ∀ L∈Ioc (0:ℝ) A,∀ p x k : ℝ,0<p → 0≤k → ∀ j : Fin 4,
        ‖radialTransfer q br amp w j p L x k‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  classical
  choose G hG hg using (fun (j : Fin 5) (d : Bool) => outer_angular_product_bound q br amp j d (N+2))
  let H := ∑ j : Fin 5,∑ d : Bool,G j d
  have hH : 0≤H := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hG j d))
  have hjH (j : Fin 5) (d : Bool) : G j d≤H := by
    exact (Finset.single_le_sum (fun e _ => hG j e) (Finset.mem_univ d)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun e _ => hG l e)) (Finset.mem_univ j))
  refine ⟨H,hH,?_⟩
  intro w hw A hA
  choose B hB hb using (fun (j : Fin 5) (d : Bool) => hg j d w (by linarith [hjH j d]) A hA)
  obtain ⟨D,hD,hd⟩ := outer_forcing_product_bound q br amp w true (N+2) (by linarith) A hA
  let M := (∑ j : Fin 5,∑ d : Bool,B j d)+D
  have hM : 0≤M := add_nonneg (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hB j d))) hD
  have hjM (j : Fin 5) (d : Bool) : B j d≤M := by
    have h := (Finset.single_le_sum (fun e _ => hB j e) (Finset.mem_univ d)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun e _ => hB l e)) (Finset.mem_univ j))
    exact h.trans (le_add_of_nonneg_right hD)
  have hDM : D≤M := le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hB j d)))
  refine ⟨3*M,by positivity,?_⟩
  intro L hL p x k hp hk j
  let E := M*Real.exp (-(N:ℝ)*k)*Real.exp (-p)
  have hE : 0≤E := by dsimp [E];positivity
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
      ‖Complex.exp (-w*(p:ℂ))*angularProduct q br amp w l d p L x k‖≤E := by
    apply (hb l d L hL p x k hp.le hk).trans
    dsimp [E]
    gcongr
    exact hjM l d
  have hc2 : ‖Complex.exp (2*(k:ℂ))*(Complex.exp (-w*(p:ℂ))*
      angularProduct q br amp w 2 true p L x k)‖≤E := by
    rw [norm_mul,show ‖Complex.exp (2*(k:ℂ))‖=Real.exp (2*k) by simp [Complex.norm_exp]]
    calc
      _ ≤ Real.exp (2*k)*(M*Real.exp (-((N+2:ℕ):ℝ)*k)*Real.exp (-p)) := by
        gcongr
        exact (hb 2 true L hL p x k hp.le hk).trans (by gcongr;exact hjM 2 true)
      _ = E := by
        rw [show Real.exp (2*k)*(M*Real.exp (-((N+2:ℕ):ℝ)*k)*Real.exp (-p))=
          M*(Real.exp (2*k)*Real.exp (-((N+2:ℕ):ℝ)*k))*Real.exp (-p) by ring,h2k]
  have hc1 : ‖Complex.exp (-(k:ℂ))*(Complex.exp (-w*(p:ℂ))*
      angularProduct q br amp w 1 false p L x k)‖≤E := by
    have he : ‖Complex.exp (-(k:ℂ))‖≤1 := by
      rw [Complex.norm_exp]
      simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hk)
    rw [norm_mul]
    exact (mul_le_mul he (hc 1 false) (norm_nonneg _) (by norm_num)).trans_eq (one_mul E)
  have hf : ‖Complex.exp (-w*(p:ℂ))*normalizedProduct q br amp w true p L x k‖≤E := by
    apply (hd L hL p x k hp.le hk).trans
    dsimp [E]
    gcongr
  have hgoal : 3*E=(3*M)*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by dsimp [E];ring
  rw [← hgoal]
  fin_cases j
  · simpa [radialTransfer,normalizedTransfer] using (hc 0 true).trans (by nlinarith : E≤3*E)
  · change ‖radialTransfer q br amp w 1 p L x k‖≤3*E
    have he : radialTransfer q br amp w 1 p L x k=
        Complex.exp (-(k:ℂ))*(Complex.exp (-w*(p:ℂ))*angularProduct q br amp w 1 false p L x k) := by
      simp [radialTransfer,normalizedTransfer];ring
    rw [he]
    exact hc1.trans (by nlinarith)
  · change ‖radialTransfer q br amp w 2 p L x k‖≤3*E
    have he : radialTransfer q br amp w 2 p L x k=
        Complex.exp (2*(k:ℂ))*(Complex.exp (-w*(p:ℂ))*angularProduct q br amp w 2 true p L x k)+
        Complex.exp (-w*(p:ℂ))*angularProduct q br amp w 3 true p L x k-
        Complex.exp (-w*(p:ℂ))*angularProduct q br amp w 1 true p L x k := by
      simp [radialTransfer,normalizedTransfer];ring
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      ((add_le_add (add_le_add hc2 (hc 3 true)) (hc 1 true)).trans_eq (by ring)))
  · simpa [radialTransfer,normalizedTransfer] using hf.trans (by nlinarith : E≤3*E)

private theorem remove_exp (C p : ℝ) (hC : 0≤C) (hp : 0≤p) : C*Real.exp (-p)≤C :=
  (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)) hC).trans_eq (mul_one C)

/-- Both endpoint corrections and all four time moments of the complete
physical horizon boundary retain uniform arbitrary cusp decay. -/
theorem outer_boundary_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∀ A : ℝ,0<A → ∃ C : ℝ,0≤C ∧
      ∀ L∈Ioc (0:ℝ) A,∀ a b k : ℝ,0<a → a≤b → 0≤k → ‖radialBoundary q br amp w a b L k‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := outer_transfer_bound q br amp N
  refine ⟨G,hG,?_⟩
  intro w hw A hA
  obtain ⟨C,hC,hc⟩ := hg w hw A hA
  let mu := D4BMLeftModeRadialEquation.eigenvalue q
  let lam := mu-2
  let B := 2*‖lam‖*C+‖w‖*(‖mu‖+2+2*‖lam‖)*C
  have hB : 0≤B := by dsimp [B];positivity
  refine ⟨B,hB,?_⟩
  intro L hL a b k ha hab hk
  let E := C*Real.exp (-(N:ℝ)*k)
  have hE : 0≤E := by dsimp [E];positivity
  let F := fun j p => ∫ x in (-1/2:ℝ)..1/2,radialTransfer q br amp w j p L x k
  have hF (j : Fin 4) (p : ℝ) (hp : 0<p) : ‖F j p‖≤E*Real.exp (-p) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun x _ => hc L hL p x k hp hk j)
    simpa only [F,E,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one,neg_div] using h
  have hF' (j : Fin 4) (p : ℝ) (hp : 0<p) : ‖F j p‖≤E := (hF j p hp).trans (remove_exp E p hE hp.le)
  have hI (j : Fin 4) : ‖∫ p in a..b,F j p‖≤E :=
    (exponential_interval_bound (F j) E a b hE hab (fun p hp => hF j p (ha.trans_le hp.1))).trans
      (remove_exp E a hE ha.le)
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
    _ ≤ ‖lam‖*(E+E)+‖w‖*((‖mu‖*E+E)+2*‖lam‖*E+E) := by
      gcongr
      · exact hF' 0 b (ha.trans_le hab)
      · exact hF' 0 a ha
      all_goals exact hI _
    _ = B*Real.exp (-(N:ℝ)*k) := by dsimp [B,E];ring


/-- The complete original boundary is radially admitted through the outer
endpoint on the actual moving static-time triangle, with uniform cusp decay. -/
theorem outer_static_boundary_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ A : ℝ,0<A →
      ∃ C : ℝ,0≤C ∧ ∀ a T k : ℝ,0<a → 0≤k →
        IntervalIntegrable (fun L => radialBoundary q br amp w a (max a (T-L/2)) L k) volume 0 A ∧
        ‖∫ L in (0:ℝ)..A,radialBoundary q br amp w a (max a (T-L/2)) L k/2‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := outer_boundary_bound q br amp N
  refine ⟨G,hG,?_⟩
  intro w hwi hw A hA
  obtain ⟨C,hC,hc⟩ := hg w hw A hA
  refine ⟨A*C/2,by positivity,?_⟩
  intro a T k ha hk
  let f := fun L => radialBoundary q br amp w a (max a (T-L/2)) L k
  have hf : ContinuousOn f (Ioi (0:ℝ)) := by
    intro L hL
    have hLp : 0<L := hL
    have h := static_boundary_radial_continuous q br amp w hwi k (L/2) (L+1) a T (by linarith) ha
    exact (h.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioc (0:ℝ) A)) :=
    (hf.mono (fun _ h => h.1)).aestronglyMeasurable measurableSet_Ioc
  have hb (L : ℝ) (hL : L∈Ioc (0:ℝ) A) : ‖f L‖≤C*Real.exp (-(N:ℝ)*k) :=
    hc L hL a (max a (T-L/2)) k ha (le_max_left _ _) hk
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mpr
    apply (integrable_const (C*Real.exp (-(N:ℝ)*k))).mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    exact hb L hL
  · have hi := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) hA.le
      (Filter.Eventually.of_forall (fun L (hL : L∈Ioc (0:ℝ) A) => hb L hL)) (intervalIntegrable_const)
    rw [intervalIntegral.integral_div,norm_div]
    have htwo : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
    rw [htwo]
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
    calc
      _ ≤ (A*(C*Real.exp (-(N:ℝ)*k)))/2 := div_le_div_of_nonneg_right hi (by norm_num)
      _ = _ := by ring

end
end RHTower.D4BMOriginalOuterCuspBoundary
