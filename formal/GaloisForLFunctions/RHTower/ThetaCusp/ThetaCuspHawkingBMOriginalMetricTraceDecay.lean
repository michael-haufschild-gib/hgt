import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonProductDecay
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalFullCollarRestoration

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalMetricTraceDecay
open D4BMJointSource D4BMModularCore D4BMOriginalHorizonProductDecay
open D4BMOriginalBoundaryCollarBounds D4BMOriginalBoundaryRestoration
open D4BMOriginalAngularProducts D4BMOriginalForcingProductBounds
open D4BMOriginalSourceRadialAdmission D4BMOriginalSourceRadialRestoration
open D4BMOriginalSourceTailCollar D4BMOriginalFullMetricCollar
noncomputable section
set_option autoImplicit false

/-- The actual four horizon transfers have arbitrary cusp decay, uniformly
for all positive source times in one derived convergence half-plane. -/
theorem horizon_transfer_decay (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧
      ∀ p x k : ℝ,0<p → 0≤k → ∀ j : Fin 4,
        ‖horizonTransfer q br amp w j p x k‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  classical
  choose G hG hg using (fun (j : Fin 5) (d : Bool) => horizon_angular_product_decay q br amp j d (N+2))
  let H := ∑ j : Fin 5,∑ d : Bool,G j d
  have hH : 0≤H := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hG j d))
  have hjH (j : Fin 5) (d : Bool) : G j d≤H := by
    exact (Finset.single_le_sum (fun e _ => hG j e) (Finset.mem_univ d)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun e _ => hG l e)) (Finset.mem_univ j))
  refine ⟨H,hH,?_⟩
  intro w hw
  choose B hB hb using (fun (j : Fin 5) (d : Bool) => hg j d w (by linarith [hjH j d]))
  obtain ⟨D,hD,hd⟩ := horizon_forcing_product_decay q br amp w true (N+2) (by linarith)
  let M := (∑ j : Fin 5,∑ d : Bool,B j d)+D
  have hM : 0≤M := add_nonneg (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hB j d))) hD
  have hjM (j : Fin 5) (d : Bool) : B j d≤M := by
    have h := (Finset.single_le_sum (fun e _ => hB j e) (Finset.mem_univ d)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun e _ => hB l e)) (Finset.mem_univ j))
    exact h.trans (le_add_of_nonneg_right hD)
  have hDM : D≤M := le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun d _ => hB j d)))
  refine ⟨3*M,by positivity,?_⟩
  intro p x k hp hk j
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
      ‖Complex.exp (-w*(p:ℂ))*horizonAngularProduct q br amp w l d p x k‖≤E := by
    apply (hb l d p x k hp hk).trans
    dsimp [E]
    gcongr
    exact hjM l d
  have hc2 : ‖Complex.exp (2*(k:ℂ))*(Complex.exp (-w*(p:ℂ))*
      horizonAngularProduct q br amp w 2 true p x k)‖≤E := by
    rw [norm_mul,show ‖Complex.exp (2*(k:ℂ))‖=Real.exp (2*k) by simp [Complex.norm_exp]]
    calc
      _ ≤ Real.exp (2*k)*(M*Real.exp (-((N+2:ℕ):ℝ)*k)*Real.exp (-p)) := by
        gcongr
        exact (hb 2 true p x k hp hk).trans (by gcongr;exact hjM 2 true)
      _ = E := by
        rw [show Real.exp (2*k)*(M*Real.exp (-((N+2:ℕ):ℝ)*k)*Real.exp (-p))=
          M*(Real.exp (2*k)*Real.exp (-((N+2:ℕ):ℝ)*k))*Real.exp (-p) by ring,h2k]
  have hc1 : ‖Complex.exp (-(k:ℂ))*(Complex.exp (-w*(p:ℂ))*
      horizonAngularProduct q br amp w 1 false p x k)‖≤E := by
    have he : ‖Complex.exp (-(k:ℂ))‖≤1 := by
      rw [Complex.norm_exp]
      simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hk)
    rw [norm_mul]
    exact (mul_le_mul he (hc 1 false) (norm_nonneg _) (by norm_num)).trans_eq (one_mul E)
  have hf : ‖Complex.exp (-w*(p:ℂ))*horizonProduct q br amp w true p x k‖≤E := by
    apply (hd p x k hp hk).trans
    dsimp [E]
    gcongr
  have hgoal : 3*E=(3*M)*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by dsimp [E];ring
  rw [← hgoal]
  fin_cases j
  · simpa [horizonTransfer] using (hc 0 true).trans (by nlinarith : E≤3*E)
  · change ‖horizonTransfer q br amp w 1 p x k‖≤3*E
    have he : horizonTransfer q br amp w 1 p x k=
        Complex.exp (-(k:ℂ))*(Complex.exp (-w*(p:ℂ))*horizonAngularProduct q br amp w 1 false p x k) := by
      simp [horizonTransfer];ring
    rw [he]
    exact hc1.trans (by nlinarith)
  · change ‖horizonTransfer q br amp w 2 p x k‖≤3*E
    have he : horizonTransfer q br amp w 2 p x k=
        Complex.exp (2*(k:ℂ))*(Complex.exp (-w*(p:ℂ))*horizonAngularProduct q br amp w 2 true p x k)+
        Complex.exp (-w*(p:ℂ))*horizonAngularProduct q br amp w 3 true p x k-
        Complex.exp (-w*(p:ℂ))*horizonAngularProduct q br amp w 1 true p x k := by
      simp [horizonTransfer];ring
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      ((add_le_add (add_le_add hc2 (hc 3 true)) (hc 1 true)).trans_eq (by ring)))
  · simpa [horizonTransfer] using hf.trans (by nlinarith : E≤3*E)

private theorem remove_exp (C p : ℝ) (hC : 0≤C) (hp : 0≤p) : C*Real.exp (-p)≤C :=
  (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)) hC).trans_eq (mul_one C)

/-- Both endpoint corrections and all four time moments of the complete
physical horizon boundary retain uniform arbitrary cusp decay. -/
theorem horizon_boundary_decay (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧
      ∀ a b k : ℝ,0<a → a≤b → 0≤k → ‖horizonBoundary q br amp w a b k‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := horizon_transfer_decay q br amp N
  refine ⟨G,hG,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := hg w hw
  let mu := D4BMLeftModeRadialEquation.eigenvalue q
  let lam := mu-2
  let B := 2*‖lam‖*C+‖w‖*(‖mu‖+2+2*‖lam‖)*C
  have hB : 0≤B := by dsimp [B];positivity
  refine ⟨B,hB,?_⟩
  intro a b k ha hab hk
  let A := C*Real.exp (-(N:ℝ)*k)
  have hA : 0≤A := by dsimp [A];positivity
  let F := fun j p => ∫ x in (-1/2:ℝ)..1/2,horizonTransfer q br amp w j p x k
  have hF (j : Fin 4) (p : ℝ) (hp : 0<p) : ‖F j p‖≤A*Real.exp (-p) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun x _ => hc p x k hp hk j)
    simpa only [F,A,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one,neg_div] using h
  have hF' (j : Fin 4) (p : ℝ) (hp : 0<p) : ‖F j p‖≤A := (hF j p hp).trans (remove_exp A p hA hp.le)
  have hI (j : Fin 4) : ‖∫ p in a..b,F j p‖≤A :=
    (exponential_interval_bound (F j) A a b hA hab (fun p hp => hF j p (ha.trans_le hp.1))).trans
      (remove_exp A a hA ha.le)
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
    _ = B*Real.exp (-(N:ℝ)*k) := by dsimp [B,A];ring

/-- The complete source horizon functional retains the two temporal endpoints
and has the same uniform cusp decay as its original admitted period. -/
theorem horizon_source_decay (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧
      ∀ a b k : ℝ,0<a → a≤b → 0≤k → ‖horizonSourceFunctional q br amp w a b k‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := horizon_period_bound q br amp N
  refine ⟨G,hG,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := hg w hw
  let mu := D4BMLeftModeRadialEquation.eigenvalue q
  refine ⟨‖mu*(mu-2)‖*(2+‖2*w‖)*C,by positivity,?_⟩
  intro a b k ha hab hk
  let A := C*Real.exp (-(N:ℝ)*k)
  have hA : 0≤A := by dsimp [A];positivity
  have hp (p : ℝ) (hp : 0<p) : ‖horizonPeriodError q br amp w p k‖≤A :=
    (hc p k hp hk).trans (remove_exp A p hA hp.le)
  have hi : ‖∫ p in a..b,horizonPeriodError q br amp w p k‖≤A :=
    (exponential_interval_bound _ A a b hA hab (fun p hp => hc p k (ha.trans_le hp.1) hk)).trans (remove_exp A a hA ha.le)
  change ‖mu*(mu-2)*(horizonPeriodError q br amp w b k-horizonPeriodError q br amp w a k+
    2*w*(∫ p in a..b,horizonPeriodError q br amp w p k))‖≤_
  rw [norm_mul]
  calc
    _ ≤ ‖mu*(mu-2)‖*((A+A)+‖2*w‖*A) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add (hp b (ha.trans_le hab)) (hp a ha)))
        (by rw [norm_mul];gcongr))
    _ = _ := by dsimp [A];ring

/-- The entire metric horizon trace, with no cancellation premise and no
chosen relation between temporal cutoffs, has arbitrary cusp decay. -/
theorem metric_trace_decay (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧
      ∀ a b k : ℝ,0<a → a≤b → 0≤k → ‖metricTrace q br amp w a b k‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G1,hG1,h1⟩ := horizon_source_decay q br amp N
  obtain ⟨G2,_,h2⟩ := horizon_boundary_decay q br amp N
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := h1 w (by linarith [le_max_left G1 G2])
  obtain ⟨D,hD,hd⟩ := h2 w (by linarith [le_max_right G1 G2])
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro a b k ha hab hk
  exact (norm_add_le _ _).trans ((add_le_add (hc a b k ha hab hk) (hd a b k ha hab hk)).trans_eq (by ring))

end
end RHTower.D4BMOriginalMetricTraceDecay
