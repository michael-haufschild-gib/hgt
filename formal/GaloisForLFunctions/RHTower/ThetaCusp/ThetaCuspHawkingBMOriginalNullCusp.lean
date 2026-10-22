import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCuspJets

/-!
Cusp control of the genuine null derivatives of the original causal remainder.

The original Goursat identities express both response derivatives as single
integrals of the remainder forcing. Its angular jets supply arbitrary decay;
the complete principal subtraction and differentiated onset lift are retained.
The bounds are uniform on bounded positive causal rectangles and in horizontal
position. They admit arbitrary complex cusp weights and varying bounded paths.
Infinite-time, horizon and moving-corner matching are not asserted here.
-/

open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMOriginalNullCusp
open D4BMCausalCusp D4BMNativeCuspJets D4BMNativeCircle D4BMNativeResponse
open D4BMSquareCuspJets D4BMJointSource D4BMOriginalCausalPotential
open D4BMNativeAngularCurrent D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private abbrev F := ℝ → ℝ → ℝ → ℝ → ℂ
private def Rapid (T : Ici (0:ℝ)) (f : F) : Prop :=
  ∀ N : ℕ, ∃ D B : ℝ, 0≤D ∧ 0≤B ∧
    ∀ p ∈ Icc 0 T.val, ∀ r ∈ Icc 0 T.val, ∀ X k : ℝ, D≤k →
      ‖f p r X k‖≤B*Real.exp (-(N:ℝ)*k)

private theorem rapid_add {T : Ici (0:ℝ)} {f g : F} (hf : Rapid T f) (hg : Rapid T g) :
    Rapid T (fun p r X k => f p r X k+g p r X k) := by
  intro N
  obtain ⟨D,B,hD,hB,hf⟩ := hf N
  obtain ⟨E,C,hE,hC,hg⟩ := hg N
  refine ⟨max D E,B+C,le_trans hD (le_max_left _ _),add_nonneg hB hC,?_⟩
  intro p hp r hr X k hk
  calc
    _ ≤ ‖f p r X k‖+‖g p r X k‖ := norm_add_le _ _
    _ ≤ B*Real.exp (-(N:ℝ)*k)+C*Real.exp (-(N:ℝ)*k) :=
      add_le_add (hf p hp r hr X k ((le_max_left _ _).trans hk))
        (hg p hp r hr X k ((le_max_right _ _).trans hk))
    _ = _ := by ring

private theorem rapid_neg {T : Ici (0:ℝ)} {f : F} (hf : Rapid T f) :
    Rapid T (fun p r X k => -f p r X k) := by
  simpa only [Rapid,norm_neg] using hf

private theorem rapid_mul {T : Ici (0:ℝ)} {f : F} (hf : Rapid T f)
    (c : ℝ → ℝ → ℂ) (hc : Continuous (Function.uncurry c)) :
    Rapid T (fun p r X k => c p r*f p r X k) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc 0 T.val ×ˢ Icc 0 T.val) hc.continuousOn
  intro N
  obtain ⟨D,B,hD,hB,hf⟩ := hf N
  refine ⟨D,max C 0*B,hD,mul_nonneg (le_max_right _ _) hB,?_⟩
  intro p hp r hr X k hk
  rw [norm_mul]
  calc
    _ ≤ max C 0*(B*Real.exp (-(N:ℝ)*k)) :=
      mul_le_mul ((hC (p,r) ⟨hp,hr⟩).trans (le_max_left _ _))
        (hf p hp r hr X k hk) (norm_nonneg _) (le_max_right _ _)
    _ = _ := by ring

private theorem rapid_height_square {T : Ici (0:ℝ)} {f : F} (hf : Rapid T f) :
    Rapid T (fun p r X k => (Real.exp k:ℂ)^(2 : ℕ)*f p r X k) := by
  intro N
  obtain ⟨D,B,hD,hB,hf⟩ := hf (N+2)
  refine ⟨D,B,hD,hB,?_⟩
  intro p hp r hr X k hk
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp k)^(2 : ℕ)*(B*Real.exp (-((N+2:ℕ):ℝ)*k)) := by
      exact mul_le_mul_of_nonneg_left (hf p hp r hr X k hk) (sq_nonneg _)
    _ = B*Real.exp (-(N:ℝ)*k) := by
      rw [pow_two,← Real.exp_add]
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      push_cast
      ring

private theorem response_rapid (q : XiZeroCopy) (s amp : ℂ) (word : List (Fin 2))
    (T : Ici (0:ℝ)) :
    Rapid T (fun p r X k => coordinateJet word (responseRemainder q s amp p r) ![X,k]) := by
  intro N
  obtain ⟨D,B,hD,hB,hf⟩ := responseRemainder_jet_uniform_bound q s amp word N T
  refine ⟨D,B*Real.exp ((N:ℝ)*D),hD,by positivity,?_⟩
  intro p hp r hr X k hk
  calc
    _ ≤ B*Real.exp ((N:ℝ)*(D-k)) := hf p hp r hr X k hk
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring

private theorem native_rapid (q : XiZeroCopy) (T : Ici (0:ℝ)) :
    Rapid T (fun _ _ X k => nativeRemainder q ![0,X,k]) := by
  intro N
  obtain ⟨B,hB,hf⟩ := nativeCuspJet_rapid_bound q [] N ⟨0,show (0:ℝ)≤0 from le_rfl⟩
  refine ⟨0,B,le_rfl,hB,?_⟩
  intro p hp r hr X k hk
  simpa only [nativeJet,nativeRemainder,Matrix.cons_val,zero_sub,mul_neg,neg_mul] using
    hf 0 X k le_rfl le_rfl hk

private theorem weight_continuous (s amp : ℂ) :
    Continuous (fun z : ℝ × ℝ => sourceWeight s amp z.1 z.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,min ((z.1-z.2)/2) 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,min (-((z.1-z.2)/2)) 0)) by fun_prop)
  convert! h₁.sub h₂ using 1

private theorem forcing_rapid (q : XiZeroCopy) (s amp : ℂ) (T : Ici (0:ℝ)) :
    Rapid T (fun p r X k => remainderForcing q s amp p r ![X,k]) := by
  have hs := rapid_mul (native_rapid q T) (fun p r => (1/4:ℂ)*sourceWeight s amp p r)
    (continuous_const.mul (weight_continuous s amp))
  have ha := rapid_add (rapid_add (rapid_height_square (response_rapid q s amp [0,0] T))
    (response_rapid q s amp [1,1] T)) (rapid_neg (response_rapid q s amp [1] T))
  have hc : Continuous (fun z : ℝ × ℝ => (1:ℂ)/(4*(Real.cosh ((z.1-z.2)/2):ℂ)^(2 : ℕ))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  have h := rapid_add hs (rapid_mul ha (fun p r => (1:ℂ)/(4*(Real.cosh ((p-r)/2):ℂ)^(2 : ℕ))) hc)
  convert h using 1
  funext p r X k
  dsimp only [remainderForcing,Matrix.cons_val]
  ring

private theorem integral_bound (T : Ici (0:ℝ)) {f : ℝ → ℂ} {r C : ℝ}
    (hr : r∈Icc 0 T.val) (hC : 0≤C) (hf : ∀ b∈Icc 0 r, ‖f b‖≤C) :
    ‖∫ b in (0:ℝ)..r, f b‖≤C*T.val := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := r) (C := C) (by
      intro b hb
      rw [uIoc_of_le hr.1] at hb
      exact hf b ⟨hb.1.le,hb.2⟩)
  simp only [sub_zero,abs_of_nonneg hr.1] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr.2 hC)

/-- Both genuine null derivatives of the complete response remainder have
arbitrary cusp decay, uniformly on positive bounded causal rectangles. -/
theorem response_null_cusp_bound (q : XiZeroCopy) (s amp : ℂ) (T : Ici (0:ℝ)) (N : ℕ) :
    ∃ D B : ℝ, 0≤D ∧ 0≤B ∧
      ∀ p∈Ioc 0 T.val, ∀ r∈Ioc 0 T.val, ∀ X k : ℝ, D≤k →
        ‖deriv (fun a => responseRemainder q s amp a r ![X,k]) p‖≤B*Real.exp (-(N:ℝ)*k) ∧
        ‖deriv (fun b => responseRemainder q s amp p b ![X,k]) r‖≤B*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨D,B,hD,hB,hf⟩ := forcing_rapid q s amp T N
  refine ⟨D,B*T.val,hD,mul_nonneg hB T.property,?_⟩
  intro p hp r hr X k hk
  have hp' : p∈Icc 0 T.val := ⟨hp.1.le,hp.2⟩
  have hr' : r∈Icc 0 T.val := ⟨hr.1.le,hr.2⟩
  constructor
  · rw [(responseRemainder_first_null q s amp ⟨p,hp.1⟩ ⟨r,hr.1.le⟩ ![X,k]).deriv]
    have h := integral_bound T hr' (show 0≤B*Real.exp (-(N:ℝ)*k) by positivity)
      (fun b hb => hf p hp' b ⟨hb.1,hb.2.trans hr.2⟩ X k hk)
    simpa only [mul_right_comm] using h
  · rw [(responseRemainder_second_null q s amp ⟨p,hp.1.le⟩ ⟨r,hr.1⟩ ![X,k]).deriv]
    have h := integral_bound T hp' (show 0≤B*Real.exp (-(N:ℝ)*k) by positivity)
      (fun a ha => hf a ⟨ha.1,ha.2.trans hp.2⟩ r hr' X k hk)
    simpa only [mul_right_comm] using h

private theorem first_integral_rapid (q : XiZeroCopy) (s amp : ℂ) (T : Ici (0:ℝ)) :
    Rapid T (fun p r X k => ∫ b in (0:ℝ)..r, remainderForcing q s amp p b ![X,k]) := by
  intro N
  obtain ⟨D,B,hD,hB,hf⟩ := forcing_rapid q s amp T N
  refine ⟨D,B*T.val,hD,mul_nonneg hB T.property,?_⟩
  intro p hp r hr X k hk
  have h := integral_bound T hr (show 0≤B*Real.exp (-(N:ℝ)*k) by positivity)
    (fun b hb => hf p hp b ⟨hb.1,hb.2.trans hr.2⟩ X k hk)
  simpa only [mul_right_comm] using h

private theorem second_integral_rapid (q : XiZeroCopy) (s amp : ℂ) (T : Ici (0:ℝ)) :
    Rapid T (fun p r X k => ∫ a in (0:ℝ)..p, remainderForcing q s amp a r ![X,k]) := by
  intro N
  obtain ⟨D,B,hD,hB,hf⟩ := forcing_rapid q s amp T N
  refine ⟨D,B*T.val,hD,mul_nonneg hB T.property,?_⟩
  intro p hp r hr X k hk
  have h := integral_bound T hp (show 0≤B*Real.exp (-(N:ℝ)*k) by positivity)
    (fun a ha => hf a ⟨ha.1,ha.2.trans hp.2⟩ r hr X k hk)
  simpa only [mul_right_comm] using h

private def liftRight (s amp : ℂ) (p r : ℝ) : ℂ :=
  -radialLiftFirst s 0 amp 1 ((p-r)/2)*timeOnset (2*s) p/2

private theorem lift_first (s amp : ℂ) (p r : ℝ) :
    HasDerivAt (fun u => nullLift s amp u r) (nullLiftFirst s amp p r) p := by
  have ht := ((hasDerivAt_id p).sub_const r).div_const 2
  have hL := (radialLift_hasDerivAt s 0 amp 1 ((p-r)/2)).scomp p ht
  apply (hL.mul (timeOnset_hasDerivAt (2*s) p)).congr_deriv
  dsimp only [nullLiftFirst]
  simp only [Function.comp_apply,id_eq,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

private theorem lift_second (s amp : ℂ) (p r : ℝ) :
    HasDerivAt (fun u => nullLift s amp p u) (liftRight s amp p r) r := by
  have ht := ((hasDerivAt_id r).const_sub p).div_const 2
  have hL := (radialLift_hasDerivAt s 0 amp 1 ((p-r)/2)).scomp r ht
  apply (hL.mul_const (timeOnset (2*s) p)).congr_deriv
  dsimp only [liftRight]
  simp only [Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

private theorem lift_derivatives_continuous (s amp : ℂ) :
    Continuous (fun z : ℝ × ℝ => nullLiftFirst s amp z.1 z.2) ∧
    Continuous (fun z : ℝ × ℝ => liftRight s amp z.1 z.2) := by
  have hL : Continuous (radialLift s 0 amp 1) := continuous_iff_continuousAt.mpr
    (fun x => (radialLift_hasDerivAt s 0 amp 1 x).continuousAt)
  have hL1 : Continuous (radialLiftFirst s 0 amp 1) := continuous_iff_continuousAt.mpr
    (fun x => (radialLiftFirst_hasDerivAt s 0 amp 1 x).continuousAt)
  have hH : Continuous (timeOnset (2*s)) := continuous_iff_continuousAt.mpr
    (fun x => (timeOnset_hasDerivAt (2*s) x).continuousAt)
  have hH1 : Continuous (timeOnsetFirst (2*s)) := continuous_iff_continuousAt.mpr
    (fun x => (timeOnsetFirst_hasDerivAt (2*s) x).continuousAt)
  have ht : Continuous (fun z : ℝ × ℝ => (z.1-z.2)/2) := by fun_prop
  constructor
  · exact (((hL1.comp ht).mul (hH.comp continuous_fst)).div_const 2).add
      ((hL.comp ht).mul (hH1.comp continuous_fst))
  · exact (((hL1.comp ht).neg).mul (hH.comp continuous_fst)).div_const 2

private theorem restored_decomposition (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (z : Fin 2 → ℝ) :
    D4BMOriginalCuspJets.remainder q branch amp p r z=
      responseRemainder q (physicalRate q branch) amp p r z+
        nullLift (physicalRate q branch) amp p r*nativeRemainder q ![0,z 0,z 1] := by
  simpa only [coordinateJet,List.map_nil,nativeJet] using
    D4BMOriginalCuspJets.original_remainder_jet q branch amp p r [] z

private theorem restored_first (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p : Ioi (0:ℝ)) (r : Ici (0:ℝ)) (X k : ℝ) :
    HasDerivAt (fun a => D4BMOriginalCuspJets.remainder q branch amp a r.val ![X,k])
      ((∫ b in (0:ℝ)..r.val, remainderForcing q (physicalRate q branch) amp p.val b ![X,k])+
        nullLiftFirst (physicalRate q branch) amp p.val r.val*nativeRemainder q ![0,X,k]) p.val := by
  have h := (responseRemainder_first_null q (physicalRate q branch) amp p r ![X,k]).add
    ((lift_first (physicalRate q branch) amp p.val r.val).mul_const (nativeRemainder q ![0,X,k]))
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun a => restored_decomposition q branch amp a r.val ![X,k])

private theorem restored_second (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p : Ici (0:ℝ)) (r : Ioi (0:ℝ)) (X k : ℝ) :
    HasDerivAt (fun b => D4BMOriginalCuspJets.remainder q branch amp p.val b ![X,k])
      ((∫ a in (0:ℝ)..p.val, remainderForcing q (physicalRate q branch) amp a r.val ![X,k])+
        liftRight (physicalRate q branch) amp p.val r.val*nativeRemainder q ![0,X,k]) r.val := by
  have h := (responseRemainder_second_null q (physicalRate q branch) amp p r ![X,k]).add
    ((lift_second (physicalRate q branch) amp p.val r.val).mul_const (nativeRemainder q ![0,X,k]))
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun b => restored_decomposition q branch amp p.val b ![X,k])

/-- The original restored remainder, including its differentiated onset lift,
retains arbitrary cusp decay in both genuine null derivatives, uniformly in
horizontal position and throughout every bounded positive causal rectangle. -/
theorem original_null_cusp_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T : Ici (0:ℝ)) (N : ℕ) :
    ∃ D B : ℝ, 0≤D ∧ 0≤B ∧
      ∀ p∈Ioc 0 T.val, ∀ r∈Ioc 0 T.val, ∀ X k : ℝ, D≤k →
        ‖deriv (fun a => D4BMOriginalCuspJets.remainder q branch amp a r ![X,k]) p‖≤
          B*Real.exp (-(N:ℝ)*k) ∧
        ‖deriv (fun b => D4BMOriginalCuspJets.remainder q branch amp p b ![X,k]) r‖≤
          B*Real.exp (-(N:ℝ)*k) := by
  have h1 := rapid_add (first_integral_rapid q (physicalRate q branch) amp T)
    (rapid_mul (native_rapid q T) (nullLiftFirst (physicalRate q branch) amp)
      (lift_derivatives_continuous (physicalRate q branch) amp).1)
  have h2 := rapid_add (second_integral_rapid q (physicalRate q branch) amp T)
    (rapid_mul (native_rapid q T) (liftRight (physicalRate q branch) amp)
      (lift_derivatives_continuous (physicalRate q branch) amp).2)
  obtain ⟨D,B,hD,hB,h1⟩ := h1 N
  obtain ⟨E,C,hE,hC,h2⟩ := h2 N
  refine ⟨max D E,B+C,hD.trans (le_max_left _ _),add_nonneg hB hC,?_⟩
  intro p hp r hr X k hk
  have hp' : p∈Icc 0 T.val := ⟨hp.1.le,hp.2⟩
  have hr' : r∈Icc 0 T.val := ⟨hr.1.le,hr.2⟩
  constructor
  · rw [(restored_first q branch amp ⟨p,hp.1⟩ ⟨r,hr.1.le⟩ X k).deriv]
    exact (h1 p hp' r hr' X k ((le_max_left _ _).trans hk)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (Real.exp_pos _).le)
  · rw [(restored_second q branch amp ⟨p,hp.1.le⟩ ⟨r,hr.1⟩ X k).deriv]
    exact (h2 p hp' r hr' X k ((le_max_right _ _).trans hk)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (Real.exp_pos _).le)

private theorem weighted_limit {f : ℝ → ℂ}
    (hf : ∀ N : ℕ, ∃ D B : ℝ, 0≤B ∧ ∀ k : ℝ, D≤k →
      ‖f k‖≤B*Real.exp (-(N:ℝ)*k)) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*f k) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt w.re
  obtain ⟨D,B,hB,hf⟩ := hf N
  have ht := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr hN)).2 tendsto_id)
  apply squeeze_zero_norm' _ (by simpa using ht.const_mul B)
  filter_upwards [eventually_ge_atTop D] with k hk
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ Real.exp (w.re*k)*(B*Real.exp (-(N:ℝ)*k)) :=
      mul_le_mul_of_nonneg_left (hf k hk) (Real.exp_pos _).le
    _ = B*Real.exp ((w.re-(N:ℝ))*k) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring

/-- Arbitrarily weighted cusp limits of the original genuine null derivatives
hold along all bounded positive null-time paths and arbitrary horizontal paths.
No regularity or convergence of these paths is assumed. -/
theorem original_null_cusp_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T : Ici (0:ℝ)) (p r : ℝ → Ioc 0 T.val) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      deriv (fun a => D4BMOriginalCuspJets.remainder q branch amp a (r k).val ![X k,k]) (p k).val)
      atTop (𝓝 0) ∧
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      deriv (fun b => D4BMOriginalCuspJets.remainder q branch amp (p k).val b ![X k,k]) (r k).val)
      atTop (𝓝 0) := by
  constructor
  · apply weighted_limit _ w
    intro N
    obtain ⟨D,B,hD,hB,h⟩ := original_null_cusp_bound q branch amp T N
    exact ⟨D,B,hB,fun k hk => (h (p k).val (p k).property (r k).val (r k).property (X k) k hk).1⟩
  · apply weighted_limit _ w
    intro N
    obtain ⟨D,B,hD,hB,h⟩ := original_null_cusp_bound q branch amp T N
    exact ⟨D,B,hB,fun k hk => (h (p k).val (p k).property (r k).val (r k).property (X k) k hk).2⟩

end
end RHTower.D4BMOriginalNullCusp
