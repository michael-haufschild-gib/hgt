import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalPrincipalMatching
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCollarCurrentBounds

/-!
Uniform coupling of the unchanged normalizable reader to the canonical source.

All five actual base operations are taken on the original restored remainder.
The full radial reader retains both horizon branches. Its product error has
arbitrary independent cusp decay and an integrable time majorant, uniformly
over the upper time cutoff. The frequency half-plane is derived from the source
bound. This does not supply the complete angular counterterms or QNM matching.
-/

open Set Filter Topology
namespace RHTower.D4BMOriginalReaderCuspBounds
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMOriginalBaseCircleJets
open D4BMOriginalHorizonForcingBound D4BMOriginalPrincipalMatching D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- The original normalizable radial reader in the ingoing-time convention. -/
def reader (q : XiZeroCopy) (w : ℂ) (L : ℝ) : ℂ :=
  Complex.exp (w*((-L/2:ℝ):ℂ))*tortoiseMode true w (physicalRadialFrequency q) (-L/2)

/-- Its actual opposite-branch horizon coefficient. -/
def horizonReader (q : XiZeroCopy) (w : ℂ) : ℂ :=
  (connection w (physicalRadialFrequency q)/(2*w))*power (-w) 2

/-- Actual canonical source jets, before angular averaging or any cutoff limit. -/
def sourceJet (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (p L x k : ℝ) : ℂ :=
  baseOperator j (fun x k => D4BMOriginalCuspJets.remainder q br amp p (p+L) ![x,k]) x k

def horizonJet (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (p x k : ℝ) : ℂ :=
  baseOperator j (actionRemainder (center q) (physicalRate q br) amp p 0) x k

/-- The unchanged radial reader times the actual canonical source has a joint
horizon error uniform in all angular positions, arbitrary cusp order and all times. -/
theorem original_reader_source_jet_error (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (N : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p x k : ℝ, 0 < p → 0 ≤ k →
      ‖Complex.exp (-w*(p:ℂ))*(reader q w L*sourceJet q br amp j p L x k-
        horizonReader q w*horizonJet q br amp j p x k)‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨C,G,hC,hG,hbound⟩ := original_action_base_jet_horizon_estimate (center q) (physicalRate q br) amp j N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨D,hD,hd⟩ := D4BMOriginalCollarCurrentBounds.normalizable_reader_collar_error w (physicalRadialFrequency q) hwi
  let beta := horizonReader q w
  let K := ‖beta‖+2*D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(K+D)*C,by positivity,?_⟩
  have hr : ∀ᶠ L : ℝ in atTop, Real.exp (-L) < 1/4 :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/4))
  filter_upwards [hd,hr,eventually_gt_atTop (0:ℝ)] with L hreader hr hL p x k hp hk
  let S := Real.exp (-L)+Real.exp (-w.re*L)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hS2 : S ≤ 2 := by
    have h1 : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : Real.exp (-w.re*L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    dsimp [S]
    linarith
  have he : ‖reader q w L-beta‖ ≤ D*S := hreader
  have hn : ‖reader q w L‖ ≤ K := by
    have ht := norm_sub_norm_le (reader q w L) beta
    have hm := mul_le_mul_of_nonneg_left hS2 hD
    dsimp [K]
    linarith
  have hsource : sourceJet q br amp j p L x k=
      baseOperator j (actionRemainder (center q) (physicalRate q br) amp p (Real.exp (-L))) x k := by
    have heq : (fun x k => D4BMOriginalCuspJets.remainder q br amp p (p+L) ![x,k])=
        actionRemainder (center q) (physicalRate q br) amp p (Real.exp (-L)) := by
      funext x k
      exact (actionRemainder_eq_original q br amp ⟨p,hp.le⟩ ⟨L,hL.le⟩ hp hr.le x k).symm
    unfold sourceJet
    rw [heq]
  have hv : ‖sourceJet q br amp j p L x k-horizonJet q br amp j p x k‖ ≤
      C*Real.exp (G*p-(N:ℝ)*k)*Real.exp (-L) := by
    rw [hsource]
    simpa only [horizonJet,abs_of_pos (Real.exp_pos _)] using
      (hbound p (Real.exp (-L)) x k hp.le (by linarith [Real.exp_pos (-L)]) hr.le hk).2
  have hz : ‖horizonJet q br amp j p x k‖ ≤ C*Real.exp (G*p-(N:ℝ)*k) :=
    (hbound p 0 x k hp.le (by norm_num) (by norm_num) hk).1
  have hnorm : ‖reader q w L*sourceJet q br amp j p L x k-beta*horizonJet q br amp j p x k‖ ≤
      ((K+D)*C)*S*Real.exp (G*p-(N:ℝ)*k) := by
    rw [show reader q w L*sourceJet q br amp j p L x k-beta*horizonJet q br amp j p x k=
      reader q w L*(sourceJet q br amp j p L x k-horizonJet q br amp j p x k)+
      (reader q w L-beta)*horizonJet q br amp j p x k by ring]
    calc
      _ ≤ ‖reader q w L‖*‖sourceJet q br amp j p L x k-horizonJet q br amp j p x k‖+
          ‖reader q w L-beta‖*‖horizonJet q br amp j p x k‖ := by
        simpa only [norm_mul] using norm_add_le
          (reader q w L*(sourceJet q br amp j p L x k-horizonJet q br amp j p x k))
          ((reader q w L-beta)*horizonJet q br amp j p x k)
      _ ≤ K*(C*Real.exp (G*p-(N:ℝ)*k)*Real.exp (-L))+
          (D*S)*(C*Real.exp (G*p-(N:ℝ)*k)) :=
        add_le_add (mul_le_mul hn hv (norm_nonneg _) hK) (mul_le_mul he hz (norm_nonneg _) (by positivity))
      _ ≤ K*(C*Real.exp (G*p-(N:ℝ)*k)*S)+(D*S)*(C*Real.exp (G*p-(N:ℝ)*k)) := by
        have hLS : Real.exp (-L) ≤ S := le_add_of_nonneg_right (Real.exp_nonneg _)
        gcongr
      _ = _ := by ring
  change ‖Complex.exp (-w*(p:ℂ))*(reader q w L*sourceJet q br amp j p L x k-beta*horizonJet q br amp j p x k)‖ ≤ _
  rw [norm_mul,Complex.norm_exp]
  have hE : (-w*(p:ℂ)).re=-w.re*p := by simp
  rw [hE]
  calc
    _ ≤ Real.exp (-w.re*p)*(((K+D)*C)*S*Real.exp (G*p-(N:ℝ)*k)) :=
      mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _)
    _ = ((K+D)*C)*S*Real.exp ((G-w.re)*p-(N:ℝ)*k) := by
      rw [show Real.exp (-w.re*p)*(((K+D)*C)*S*Real.exp (G*p-(N:ℝ)*k))=
        (((K+D)*C)*S)*(Real.exp (-w.re*p)*Real.exp (G*p-(N:ℝ)*k)) by ring,← Real.exp_add]
      congr 2
      ring
    _ ≤ ((K+D)*C)*S*Real.exp (-p-(N:ℝ)*k) := by gcongr; nlinarith
    _ = _ := by rw [show -p-(N:ℝ)*k=-(N:ℝ)*k+(-p) by ring,Real.exp_add]; ring

/-- Time integration preserves the original reader/source product and its
independent horizon and cusp error, uniformly over the upper time cutoff. -/
theorem original_reader_source_jet_time_error (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (N : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ T x k : ℝ, 0 ≤ T → 0 ≤ k →
      ‖∫ p in (0:ℝ)..T, Complex.exp (-w*(p:ℂ))*(reader q w L*sourceJet q br amp j p L x k-
        horizonReader q w*horizonJet q br amp j p x k)‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,h⟩ := original_reader_source_jet_error q br amp j N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨B,hB,h⟩ := h w hwi hw
  refine ⟨B,hB,?_⟩
  filter_upwards [h] with L hL T x k hT hk
  let C := B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi : IntervalIntegrable (fun p : ℝ => C*Real.exp (-p)) MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall (fun p hp => hL p x k hp.1 hk)) hi
  calc
    _ ≤ ∫ p in (0:ℝ)..T, C*Real.exp (-p) := hb
    _ = C*(1-Real.exp (-T)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp,neg_zero,Real.exp_zero]
    _ ≤ _ := by change C*(1-Real.exp (-T)) ≤ C; nlinarith [Real.exp_nonneg (-T)]

end
end RHTower.D4BMOriginalReaderCuspBounds
