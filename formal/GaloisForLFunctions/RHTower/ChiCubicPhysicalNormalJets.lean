import GaloisForLFunctions.RHTower.ChiCubicReciprocalPhaseJets

/-!
# All jets of the literal physical normal iterates

Exact positive dilation intertwines the physical Schwartz normal operator
with the normalized reciprocal-phase transport. The actual phase and
transport jet estimates pay every physical derivative uniformly, retaining
H^(-k) at normal order k and the entire factor 1/(N log^3 N).

All derivatives vanish outside the literal closed physical cube. Thus the
bounds hold on the whole space, with no support or regularity premise.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff LineDeriv
namespace RHTower.BAGTrace
private abbrev E := BAGPhysicalSpace
private def U : Set E := {v | 0 < v 2}
private def ax (i : Fin 3) : E := EuclideanSpace.single i 1
private def D (i : Fin 3) (f : E → ℂ) (v : E) : ℂ := fderiv ℝ f v (ax i)
private abbrev R := bagCubicNormalizedNormalOperator

private theorem U_open : IsOpen U :=
  isOpen_lt continuous_const (EuclideanSpace.proj (2 : Fin 3)).continuous
private theorem smooth_D {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) (i : Fin 3) :
    ContDiffOn ℝ ∞ (D i f) U :=
  (hf.fderiv_of_isOpen U_open (m := ∞) (by simp)).clm_apply contDiffOn_const
private theorem smooth_R (N : ℝ) {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (R N f) U :=
  (smooth_D hf 2).sub ((smooth_D (smooth_D hf 1) 0).const_smul (Complex.I/(2*Real.pi*(N : ℂ))))
private theorem D_congr (i : Fin 3) {f g : E → ℂ} {v : E} (he : f =ᶠ[𝓝 v] g) :
    D i f v = D i g v := by rw [D, D, he.fderiv_eq]
private theorem R_congr (N : ℝ) {f g : E → ℂ} (he : EqOn f g U) : EqOn (R N f) (R N g) U := by
  intro v hv
  have he' {w : E} (hw : w ∈ U) : f =ᶠ[𝓝 w] g :=
    Filter.mem_of_superset (U_open.mem_nhds hw) he
  have heD : D 1 f =ᶠ[𝓝 v] D 1 g := by
    filter_upwards [U_open.mem_nhds hv] with w hw
    exact D_congr 1 (he' hw)
  change D 2 f v - _*D 0 (D 1 f) v = D 2 g v - _*D 0 (D 1 g) v
  rw [D_congr 2 (he' hv), D_congr 0 heD]
private theorem R_iterate_congr (N : ℝ) (k : ℕ) {f g : E → ℂ}
    (he : EqOn f g U) : EqOn ((R N)^[k] f) ((R N)^[k] g) U := by
  induction k with
  | zero => exact he
  | succ k ih => simpa only [Function.iterate_succ_apply'] using R_congr N ih

private theorem D_const_mul (i : Fin 3) (c : ℂ) {f : E → ℂ} {v : E}
    (hf : DifferentiableAt ℝ f v) : D i (fun w => c*f w) v = c*D i f v := by
  unfold D
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  rfl

private theorem R_const_mul (N : ℝ) (c : ℂ) {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) : EqOn (R N (fun w => c*f w)) (fun w => c*R N f w) U := by
  intro v hv
  have hd {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U) {w : E} (hw : w ∈ U) :
      DifferentiableAt ℝ g w := (hg.contDiffAt (U_open.mem_nhds hw)).differentiableAt (by simp)
  have he : D 1 (fun w => c*f w) =ᶠ[𝓝 v] (fun w => c*D 1 f w) := by
    filter_upwards [U_open.mem_nhds hv] with w hw
    exact D_const_mul 1 c (hd hf hw)
  change D 2 (fun w => c*f w) v - _*D 0 (D 1 (fun w => c*f w)) v = c*(D 2 f v - _*D 0 (D 1 f) v)
  rw [D_congr 0 he, D_const_mul 0 c (hd (smooth_D hf 1) hv), D_const_mul 2 c (hd hf hv)]
  ring

private theorem R_iterate_const_mul (N : ℝ) (c : ℂ) (k : ℕ) {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) :
    EqOn ((R N)^[k] (fun w => c*f w)) (fun w => c*((R N)^[k] f) w) U := by
  have hs : ∀ j : ℕ, ContDiffOn ℝ ∞ ((R N)^[j] f) U := by
    intro j
    induction j with
    | zero => exact hf
    | succ j ih => simpa only [Function.iterate_succ_apply'] using smooth_R N ih
  induction k with
  | zero => intro v hv; rfl
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (R_congr N ih hv).trans (R_const_mul N c (hs k) hv)

private def dil (N : ℝ) : E →L[ℝ] E := N • ContinuousLinearMap.id ℝ E
private theorem D_dilate (N : ℝ) (i : Fin 3) (f : SchwartzMap E ℂ) (v : E) :
    D i (fun w => f (N • w)) v = (N : ℂ)*(∂_{ax i} f) (N • v) := by
  have h := (f.hasFDerivAt ((dil N) v)).comp v (dil N).hasFDerivAt
  change fderiv ℝ (f ∘ dil N) v (ax i) = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, dil, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, Complex.real_smul, SchwartzMap.lineDerivOp_apply_eq_fderiv]

private theorem R_dilate (N : {r : ℝ // r ≠ 0}) (f : SchwartzMap E ℂ) (v : E) :
    R N.1 (fun w => f (N.1 • w)) v =
      (N.1 : ℂ)*(bagCubicNormalOperator f) (N.1 • v) := by
  have he : D 1 (fun w => f (N.1 • w)) = fun w => (N.1 : ℂ)*(∂_{ax 1} f) (N.1 • w) :=
    funext (D_dilate N.1 1 f)
  have hd : DifferentiableAt ℝ (fun w => (∂_{ax 1} f) (N.1 • w)) v :=
    (∂_{ax 1} f).differentiableAt.comp v (dil N.1).differentiableAt
  change D 2 (fun w => f (N.1 • w)) v -
    (Complex.I/(2*Real.pi*(N.1 : ℂ)))*D 0 (D 1 (fun w => f (N.1 • w))) v = _
  rw [he, D_const_mul 0 (N.1 : ℂ) hd, D_dilate, D_dilate]
  change _ = (N.1 : ℂ)*((∂_{ax 2} f) (N.1 • v) -
    (Complex.I/(2*Real.pi : ℂ))*(∂_{ax 0} (∂_{ax 1} f)) (N.1 • v))
  have hn : (N.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr N.2
  field_simp

private theorem R_iterate_dilate (N : {r : ℝ // r ≠ 0}) (k : ℕ)
    (f : SchwartzMap E ℂ) :
    EqOn ((R N.1)^[k] (fun w => f (N.1 • w)))
      (fun w => (N.1 : ℂ)^k*(bagCubicNormalOperator^[k] f) (N.1 • w)) U := by
  induction k with
  | zero => intro v hv; simp
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply']
    rw [R_congr N.1 ih hv]
    have hf : ContDiffOn ℝ ∞ (fun w => (bagCubicNormalOperator^[k] f) (N.1 • w)) U :=
      ((bagCubicNormalOperator^[k] f).smooth ⊤ |>.comp (dil N.1).contDiff).contDiffOn
    rw [R_const_mul N.1 ((N.1 : ℂ)^k) hf hv]
    dsimp only
    rw [R_dilate N]
    rw [Function.iterate_succ_apply', pow_succ]
    ring

/-- The literal smooth physical amplitude at every admissible selected edge. -/
def bagCubicExpControlledPhysicalSchwartz (N : {r : ℝ // Real.exp 1 ≤ r})
    (H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}) : SchwartzMap BAGPhysicalSpace ℂ :=
  let hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  let hcut := bagCubicControlledBandCutoff_properties ⟨N.1,lt_trans zero_lt_one hN1⟩ H
  bagCubicPhysicalSchwartz hN1 hcut.1 hcut.2.2.2.1

/-- Every physical normal iterate retains the exact actual normalized
transport, including the reciprocal phase and all logarithmic factors. -/
theorem bagCubicControlledPhysicalSchwartz_normal_iterate (k : ℕ)
    (N : {r : ℝ // Real.exp 1 ≤ r}) (H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)})
    (v : {v : BAGPhysicalSpace // 0 < v 2}) :
    (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)) (N.1 • v.1) =
      (2*Real.pi/(N.1^(k+1)*Real.log N.1^3) : ℂ) *
        bagCubicNormalizedReciprocalPhase N.1 v.1 *
          ((bagCubicNormalizedTransport (1/N.1))^[k]
            (bagCubicNormalizedPhysicalWeight (H.1/N.1) (1/Real.log N.1))) v.1 := by
  have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN : 0 < N.1 := lt_trans zero_lt_one hN1
  have hL : 0 < Real.log N.1 := Real.log_pos hN1
  have hL1 : 1 ≤ Real.log N.1 := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) N.2
  let δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)} :=
    ⟨H.1/N.1,div_pos H.2.1 hN,(div_lt_iff₀ hN).mpr (by linarith only [H.2.2])⟩
  let h : {r : ℝ // r ∈ Icc (0 : ℝ) 1} :=
    ⟨1/Real.log N.1,div_nonneg zero_le_one hL.le,(div_le_iff₀ hL).mpr (by simpa using hL1)⟩
  let c : ℂ := 2*Real.pi/(N.1*Real.log N.1^3)
  let f := bagCubicExpControlledPhysicalSchwartz N H
  let Q := fun w => bagCubicNormalizedReciprocalPhase N.1 w * bagCubicNormalizedPhysicalWeight δ.1 h.1 w
  have hQ : ContDiffOn ℝ ∞ Q U :=
    (bagCubicNormalizedReciprocalPhase_contDiffOn N.1).mul
      (bagCubicNormalizedTransport_iterate_contDiffOn 0 δ h (1/N.1))
  have ha : EqOn (fun w => f (N.1 • w)) (fun w => c*Q w) U := by
    intro w hw
    exact (bagCubicPhysicalAmplitude_normalized_phase_weight ⟨N.1,hN1⟩ H ⟨w,hw⟩).trans (by
      dsimp only [c,Q,δ,h]; ring)
  have he : (N.1 : ℂ)^k * (bagCubicNormalOperator^[k] f) (N.1 • v.1) =
      c*(bagCubicNormalizedReciprocalPhase N.1 v.1 *
        ((bagCubicNormalizedTransport (1/N.1))^[k]
          (bagCubicNormalizedPhysicalWeight δ.1 h.1)) v.1) := by
    calc
      _ = ((R N.1)^[k] (fun w => f (N.1 • w))) v.1 :=
        (R_iterate_dilate ⟨N.1,hN.ne'⟩ k f v.2).symm
      _ = ((R N.1)^[k] (fun w => c*Q w)) v.1 := R_iterate_congr N.1 k ha v.2
      _ = c*((R N.1)^[k] Q) v.1 := R_iterate_const_mul N.1 c k hQ v.2
      _ = _ := congrArg (c*·) (bagCubicNormalizedNormalOperator_iterate_actual k ⟨N.1,hN.ne'⟩ δ h v)
  have hn : (N.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  calc
    _ = (c*(bagCubicNormalizedReciprocalPhase N.1 v.1 *
      ((bagCubicNormalizedTransport (1/N.1))^[k]
        (bagCubicNormalizedPhysicalWeight δ.1 h.1)) v.1))/(N.1 : ℂ)^k := by
      apply (eq_div_iff (pow_ne_zero k hn)).mpr
      simpa only [mul_comm] using he
    _ = _ := by dsimp only [c,δ,h]; rw [pow_succ]; field_simp; ring

private def Q (k : ℕ) (N δ h : ℝ) (v : E) : ℂ :=
  bagCubicNormalizedReciprocalPhase N v *
    ((bagCubicNormalizedTransport (1/N))^[k] (bagCubicNormalizedPhysicalWeight δ h)) v
private theorem fin_le (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
private theorem Q_smooth (k : ℕ) (N : ℝ)
    (δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r ∈ Icc (0 : ℝ) 1}) :
    ContDiffOn ℝ ∞ (Q k N δ.1 h.1) U :=
  (bagCubicNormalizedReciprocalPhase_contDiffOn N).mul
    (bagCubicNormalizedTransport_iterate_contDiffOn k δ h (1/N))

private theorem Q_jets (k n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ N : {r : ℝ // 1 ≤ r}, ∀ δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)},
      ∀ h : {r : ℝ // r ∈ Icc (0 : ℝ) 1}, 1/N.1 ≤ δ.1 →
        ∀ v : E, (∀ i, v i ∈ Icc (1 : ℝ) 2) →
          ‖iteratedFDeriv ℝ n (Q k N.1 δ.1 h.1) v‖ ≤ C*N.1^n/δ.1^k := by
  choose A hA hAb using bagCubicNormalizedReciprocalPhase_uniform_jets
  choose B hB hBb using bagCubicNormalizedTransport_uniform_jets k
  let C := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le) (hB (n-i)).le)
  refine ⟨C+1,by positivity,fun N δ h ht v hv => ?_⟩
  have hN : 0 < N.1 := lt_of_lt_of_le zero_lt_one N.2
  have hvU : v ∈ U := lt_of_lt_of_le zero_lt_one (hv 2).1
  have hδN : 1/δ.1 ≤ N.1 := (div_le_iff₀ δ.2.1).mpr (by
    have h := (div_le_iff₀ hN).mp ht
    nlinarith)
  have htab : |1/N.1| ≤ δ.1 := by rwa [abs_of_pos (div_pos zero_lt_one hN)]
  have hb := norm_iteratedFDerivWithin_mul_le (s := U)
    (bagCubicNormalizedReciprocalPhase_contDiffOn N.1)
    (bagCubicNormalizedTransport_iterate_contDiffOn k δ h (1/N.1))
    U_open.uniqueDiffOn hvU (fin_le n)
  have he (j : ℕ) (F : E → ℂ) : iteratedFDerivWithin ℝ j F U v = iteratedFDeriv ℝ j F v :=
    iteratedFDerivWithin_of_isOpen j U_open hvU
  simp only [he] at hb
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
      ‖iteratedFDeriv ℝ i (bagCubicNormalizedReciprocalPhase N.1) v‖ *
      ‖iteratedFDeriv ℝ (n-i) ((bagCubicNormalizedTransport (1/N.1))^[k]
        (bagCubicNormalizedPhysicalWeight δ.1 h.1)) v‖ := hb
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i)*N.1^n/δ.1^k := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hp : (1/δ.1)^(n-i) ≤ N.1^(n-i) := pow_le_pow_left₀ (div_nonneg zero_le_one δ.2.1.le) hδN _
      have hc : 0 ≤ ((n.choose i : ℝ)*A i*B (n-i)/δ.1^k)*N.1^i :=
        mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le)
          (hB (n-i)).le) (pow_nonneg δ.2.1.le k)) (pow_nonneg hN.le i)
      calc
        _ ≤ (n.choose i : ℝ)*(A i*N.1^i)*(B (n-i)/δ.1^(n-i+k)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hAb i N v hv) (Nat.cast_nonneg _))
            (hBb (n-i) δ h (1/N.1) htab v hv) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i).le (pow_nonneg hN.le i)))
        _ = ((n.choose i : ℝ)*A i*B (n-i)/δ.1^k)*N.1^i*(1/δ.1)^(n-i) := by
          rw [pow_add, div_pow, one_pow]; ring
        _ ≤ ((n.choose i : ℝ)*A i*B (n-i)/δ.1^k)*N.1^i*N.1^(n-i) :=
          mul_le_mul_of_nonneg_left hp hc
        _ = _ := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hin]; ring
    _ = C*N.1^n/δ.1^k := by simp only [C, Finset.sum_div, Finset.sum_mul]
    _ ≤ (C+1)*N.1^n/δ.1^k :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hN.le n))
        (pow_nonneg δ.2.1.le k)

private theorem jet_dilate (n : ℕ) (N : {r : ℝ // 0 < r})
    (f : SchwartzMap E ℂ) (v : E) :
    ‖iteratedFDeriv ℝ n (fun w => f (N.1 • w)) v‖ =
      N.1^n*‖iteratedFDeriv ℝ n f (N.1 • v)‖ := by
  have hf : ContDiff ℝ (n : ℕ∞ω) f := (f.smooth ⊤).of_le (fin_le n)
  have he := (dil N.1).iteratedFDeriv_comp_right hf v le_rfl
  change ‖iteratedFDeriv ℝ n (f ∘ dil N.1) v‖ = _
  rw [he]
  have hm (A : E [×n]→L[ℝ] ℂ) :
      A.compContinuousLinearMap (fun _ : Fin n => dil N.1) = N.1^n • A := by
    ext w
    simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply, dil, smul_apply,
      ContinuousLinearMap.id_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      A.map_smul_univ (fun _ : Fin n => N.1) w
  rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos N.2 n)]
  rfl

private theorem physical_jets_on_cube (k n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ N : {r : ℝ // Real.exp 1 ≤ r}, ∀ H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)},
      1 ≤ H.1 → ∀ v : E, (∀ i, v i ∈ Icc (1 : ℝ) 2) →
        ‖iteratedFDeriv ℝ n (bagCubicNormalOperator^[k]
          (bagCubicExpControlledPhysicalSchwartz N H)) (N.1 • v)‖ ≤ C/(N.1*Real.log N.1^3*H.1^k) := by
  obtain ⟨C,hC,hb⟩ := Q_jets k n
  refine ⟨2*Real.pi*C,mul_pos (mul_pos (by norm_num) Real.pi_pos) hC,fun N H hH v hv => ?_⟩
  have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN : 0 < N.1 := lt_trans zero_lt_one hN1
  have hL : 0 < Real.log N.1 := Real.log_pos hN1
  have hL1 : 1 ≤ Real.log N.1 := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) N.2
  let δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)} :=
    ⟨H.1/N.1,div_pos H.2.1 hN,(div_lt_iff₀ hN).mpr (by linarith only [H.2.2])⟩
  let h : {r : ℝ // r ∈ Icc (0 : ℝ) 1} :=
    ⟨1/Real.log N.1,div_nonneg zero_le_one hL.le,(div_le_iff₀ hL).mpr (by simpa using hL1)⟩
  let f := bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)
  let c : ℂ := 2*Real.pi/(N.1^(k+1)*Real.log N.1^3)
  have hvU : v ∈ U := lt_of_lt_of_le zero_lt_one (hv 2).1
  have he : (fun w => f (N.1 • w)) =ᶠ[𝓝 v] (fun w => c*Q k N.1 δ.1 h.1 w) := by
    filter_upwards [U_open.mem_nhds hvU] with w hw
    exact (bagCubicControlledPhysicalSchwartz_normal_iterate k N H ⟨w,hw⟩).trans (by
      dsimp only [c,Q,δ,h]; ring)
  have ht : 1/N.1 ≤ δ.1 := div_le_div_of_nonneg_right hH hN.le
  have hc : ‖c‖ = 2*Real.pi/(N.1^(k+1)*Real.log N.1^3) := by
    dsimp only [c]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_of_nonneg hN.le,
      Complex.norm_of_nonneg hL.le, Complex.norm_ofNat]
  have hbQ := hb ⟨N.1,hN1.le⟩ δ h ht v hv
  apply (mul_le_mul_iff_right₀ (pow_pos hN n)).mp
  calc
    _ = ‖iteratedFDeriv ℝ n (fun w => f (N.1 • w)) v‖ := (jet_dilate n ⟨N.1,hN⟩ f v).symm
    _ = ‖iteratedFDeriv ℝ n (fun w => c*Q k N.1 δ.1 h.1 w) v‖ :=
      congrArg norm ((he.iteratedFDeriv ℝ n).eq_of_nhds)
    _ = ‖c‖*‖iteratedFDeriv ℝ n (Q k N.1 δ.1 h.1) v‖ := by
      change ‖iteratedFDeriv ℝ n (fun w => c • Q k N.1 δ.1 h.1 w) v‖ = _
      rw [iteratedFDeriv_const_smul_apply' (((Q_smooth k N.1 δ h).contDiffAt
        (U_open.mem_nhds hvU)).of_le (fin_le n)), norm_smul]
    _ ≤ ‖c‖*(C*N.1^n/δ.1^k) := mul_le_mul_of_nonneg_left hbQ (norm_nonneg _)
    _ = N.1^n*((2*Real.pi*C)/(N.1*Real.log N.1^3*H.1^k)) := by
      rw [hc]
      dsimp only [δ]
      rw [div_pow, pow_succ]
      field_simp

private def physicalCube (N : ℝ) : Set E := {v | ∀ i, v i ∈ Icc N (2*N)}
private theorem physicalCube_closed (N : ℝ) : IsClosed (physicalCube N) := by
  rw [show physicalCube N = ⋂ i : Fin 3, {v : E | v i ∈ Icc N (2*N)} by
    ext v; simp [physicalCube]]
  exact isClosed_iInter (fun i => (isClosed_Icc : IsClosed (Icc N (2*N))).preimage
    (EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous)

private theorem normal_zero_off {f : SchwartzMap E ℂ} {S : Set E} (hS : IsClosed S)
    (hf : ∀ v ∉ S, f v = 0) : ∀ v ∉ S, bagCubicNormalOperator f v = 0 := by
  intro v hv
  have he {w : E} (hw : w ∉ S) : (f : E → ℂ) =ᶠ[𝓝 w] (fun _ => 0) := by
    filter_upwards [hS.isOpen_compl.mem_nhds hw] with u hu
    exact hf u hu
  have heD : D 1 f =ᶠ[𝓝 v] (fun _ => 0) := by
    filter_upwards [hS.isOpen_compl.mem_nhds hv] with w hw
    rw [D_congr 1 (he hw)]
    simp [D]
  change D 2 f v - (Complex.I/(2*Real.pi : ℂ))*D 0 (D 1 f) v = 0
  rw [D_congr 2 (he hv), D_congr 0 heD]
  simp [D]

private theorem physical_normal_off (k : ℕ) (N : {r : ℝ // Real.exp 1 ≤ r})
    (H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}) :
    ∀ v ∉ physicalCube N.1,
      (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)) v = 0 := by
  induction k with
  | zero =>
    intro v hv
    change ¬ ∀ i, v i ∈ Icc N.1 (2*N.1) at hv
    push Not at hv
    obtain ⟨i,hi⟩ := hv
    have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
    have hc := bagCubicControlledBandCutoff_properties ⟨N.1,lt_trans zero_lt_one hN1⟩ H
    have hz := hc.2.2.2.1 (v i) (fun h => hi ⟨h.1.le,h.2.le⟩)
    have hs : bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (v i) = 0 := by
      simp only [bagCubicMellinSliceValue, hz, Complex.ofReal_zero, zero_mul, zero_div]
    change bagCubicPhysicalAmplitude N.1 (bagCubicControlledBandCutoff N.1 H.1) v = 0
    fin_cases i <;> simp_all [bagCubicPhysicalAmplitude]
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using normal_zero_off (physicalCube_closed N.1) ih

/-- Every normal iterate and every jet vanish outside the literal closed
physical cube; differentiation creates no omitted support sector. -/
theorem bagCubicControlledPhysicalSchwartz_normal_jet_off (k n : ℕ)
    (N : {r : ℝ // Real.exp 1 ≤ r}) (H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)})
    (x : {v : BAGPhysicalSpace // ¬ ∀ i, v i ∈ Icc N.1 (2*N.1)}) :
    iteratedFDeriv ℝ n (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)) x.1 = 0 := by
  have he : (fun v => (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)) v)
      =ᶠ[𝓝 x.1] (fun _ => (0 : ℂ)) := by
    filter_upwards [(physicalCube_closed N.1).isOpen_compl.mem_nhds x.2] with v hv
    exact physical_normal_off k N H v hv
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]

/-- EVERY physical jet of EVERY normal iterate of the literal amplitude
has the complete moving-edge gain H^(-k), uniformly on ALL physical space.
The Gaussian, logarithmic, cutoff and coupled height factors remain. -/
theorem bagCubicControlledPhysicalSchwartz_normal_uniform_jets (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : {r : ℝ // Real.exp 1 ≤ r},
      ∀ H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}, 1 ≤ H.1 →
        ∀ x : BAGPhysicalSpace, ‖iteratedFDeriv ℝ n
          (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)) x‖ ≤
            C/(N.1*Real.log N.1^3*H.1^k) := by
  obtain ⟨C,hC,hb⟩ := physical_jets_on_cube k n
  refine ⟨C,hC,fun N H hH x => ?_⟩
  have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN : 0 < N.1 := lt_trans zero_lt_one hN1
  by_cases hx : x ∈ physicalCube N.1
  · let v : E := (1/N.1) • x
    have hv : ∀ i, v i ∈ Icc (1 : ℝ) 2 := by
      intro i
      change 1 ≤ (1/N.1)*x i ∧ (1/N.1)*x i ≤ 2
      rw [show (1/N.1)*x i = x i/N.1 by ring]
      exact ⟨(le_div_iff₀ hN).mpr (by simpa using (hx i).1),
        (div_le_iff₀ hN).mpr ((hx i).2)⟩
    have he : N.1 • v = x := by
      dsimp only [v]
      rw [smul_smul, show N.1*(1/N.1)=1 by field_simp, one_smul]
    simpa only [he] using hb N H hH v hv
  · rw [bagCubicControlledPhysicalSchwartz_normal_jet_off k n N H ⟨x,hx⟩, norm_zero]
    exact div_nonneg hC.le (mul_nonneg (mul_nonneg hN.le
      (pow_nonneg (Real.log_pos hN1).le 3)) (pow_nonneg H.2.1.le k))

end RHTower.BAGTrace
