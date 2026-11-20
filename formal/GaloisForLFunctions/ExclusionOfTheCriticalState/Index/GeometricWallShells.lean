import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConditionalOrdinateLawOnMultiplicativeBands
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheBeyondTheWallPrimeBalanceExcludesTheState

/-!
# Geometric shell statistics of the critical-state energy

A sharp interval on the logarithmic frequency axis is a difference of
two nested tails, as in the layer argument of Gabet, Ferreira Da Costa
and Lee. For a critical state the inverse-height tail law controls every
shell simultaneously. Their scaled masses converge in total variation
to a geometric sequence, including shells whose indices vary with time.
-/

noncomputable section
open Filter MeasureTheory Set Complex Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri

/-- Mass of the nth geometric dilation of the relative interval (uT,vT]. -/
def ordinateBand (F : ℝ → ℝ) (b u v T : ℝ) (n : ℕ) : ℝ :=
  ordinateBandMass F (u*b^n*T) (v*b^n*T)

private theorem band_eq {F : ℝ → ℝ} (hs : Summable (zeroValueMass F)) {b u v T : ℝ}
    (hb : 0≤b) (ht : 0≤T) (huv : u≤v) (n : ℕ) :
    ordinateBand F b u v T n = ordinateTailMass F (u*b^n*T) - ordinateTailMass F (v*b^n*T) := by
  have hsum (x : ℝ) : Summable (fun q : onLineCopies =>
      if x < |(centredZero q).im| then zeroValueMass F q else 0) :=
    hs.of_nonneg_of_le (fun q => ite_zero_nonneg (zeroValueMass_nonneg F q))
      (fun q => ite_zero_le (zeroValueMass_nonneg F q))
  have horder := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right huv (pow_nonneg hb n)) ht
  rw [ordinateTailMass,ordinateTailMass,← (hsum _).tsum_sub (hsum _),ordinateBand,ordinateBandMass]
  apply tsum_congr
  intro q
  split_ifs <;> first | ring | (exfalso; order)

/-- Uniform geometric domination of every dilation tail at once. -/
private theorem dilated_tail_error {f : ℝ → ℝ} {C b u ε : ℝ}
    (hf : Tendsto (fun t => t*f t) atTop (𝓝 C)) (hb : 1≤b) (hu : 0<u) (hε : 0<ε) :
    ∀ᶠ T : ℝ in atTop, ∀ n : ℕ,
      |T*f (u*b^n*T)-C/u*(b⁻¹)^n| ≤ ε/u*(b⁻¹)^n := by
  obtain ⟨L,hL⟩ := (Metric.tendsto_atTop.mp hf) ε hε
  filter_upwards [eventually_ge_atTop (max 0 (L/u))] with T hT
  have hT₀ := (le_max_left _ _).trans hT
  have hLT := (div_le_iff₀ hu).mp ((le_max_right _ _).trans hT)
  intro n
  have hpow : 1 ≤ b^n := one_le_pow₀ hb
  have harg : L ≤ u*b^n*T := by
    calc L ≤ T*u := hLT
         _ ≤ T*u*b^n := le_mul_of_one_le_right (mul_nonneg hT₀ hu.le) hpow
         _ = _ := by ring
  have he := (hL _ harg).le
  rw [Real.dist_eq] at he
  have hp : 0<b^n := zero_lt_one.trans_le hpow
  have hiden : T*f (u*b^n*T)-C/u*b⁻¹^n = ((u*b^n*T)*f (u*b^n*T)-C)/(u*b^n) := by
    rw [inv_pow]
    field_simp [hu.ne',hp.ne'] <;> ring
  rw [hiden,abs_div,abs_of_pos (mul_pos hu hp),inv_pow]
  exact (div_le_div_of_nonneg_right he (mul_pos hu hp).le).trans_eq (by ring)

/-- Rescaled bin errors are summable for all sufficiently late T, with
total absolute error tending to zero. The two endpoints may lie anywhere
inside one multiplicative period. -/
theorem critical_shell_total_variation {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {b u v : ℝ} (hb : 1<b) (hu : 0<u) (huv : u≤v) :
    let C := ordinateCuspConstant W F
    let err := fun (T : ℝ) (n : ℕ) =>
      |T*ordinateBand F b u v T n-C*(u⁻¹-v⁻¹)*(b⁻¹)^n|
    (∀ᶠ T : ℝ in atTop, Summable (err T)) ∧
      Tendsto (fun T => ∑' n : ℕ, err T n) atTop (𝓝 0) := by
  intro C err
  have hv := hu.trans_le huv
  have hlim : Tendsto (fun t => t*ordinateTailMass F t) atTop (𝓝 C) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  have hmass := (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  have hq : 0≤b⁻¹ := inv_nonneg.mpr (zero_le_one.trans hb.le)
  have hq1 : b⁻¹<1 := (inv_lt_one₀ (zero_lt_one.trans hb)).mpr hb
  have hseries := summable_geometric_of_lt_one hq hq1
  let A := (u⁻¹+v⁻¹)/(1-b⁻¹)
  have hA : 0<A := div_pos (add_pos (inv_pos.mpr hu) (inv_pos.mpr hv)) (sub_pos.mpr hq1)
  have bound (ε : ℝ) (he : 0<ε) : ∀ᶠ T : ℝ in atTop,
      Summable (err T) ∧ (∑' n : ℕ,err T n) ≤ ε*A := by
    filter_upwards [dilated_tail_error hlim hb.le hu he,dilated_tail_error hlim hb.le hv he,
      eventually_ge_atTop (0:ℝ)] with T h₁ h₂ hT
    let major := fun n : ℕ => (ε/u+ε/v)*(b⁻¹)^n
    have hmaj := hseries.mul_left (ε/u+ε/v)
    have hpoint (n : ℕ) : err T n ≤ major n := by
      dsimp only [err,major]
      rw [band_eq hmass (zero_le_one.trans hb.le) hT huv]
      let a := T*ordinateTailMass F (u*b^n*T)-C/u*b⁻¹^n
      let d := T*ordinateTailMass F (v*b^n*T)-C/v*b⁻¹^n
      have heq : T*(ordinateTailMass F (u*b^n*T)-ordinateTailMass F (v*b^n*T))-
          C*(u⁻¹-v⁻¹)*b⁻¹^n=a-d := by dsimp only [a,d]; ring
      rw [heq,add_mul]
      exact (abs_sub a d).trans (add_le_add (h₁ n) (h₂ n))
    have hs : Summable (err T) := hmaj.of_nonneg_of_le (fun _ => abs_nonneg _) hpoint
    refine ⟨hs,(hs.tsum_le_tsum hpoint hmaj).trans_eq ?_⟩
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq hq1]
    dsimp only [A]; ring
  refine ⟨(bound 1 zero_lt_one).mono (fun _ h => h.1),Metric.tendsto_atTop.mpr ?_⟩
  intro ε he
  obtain ⟨L,hL⟩ := eventually_atTop.mp (bound (ε/(2*A)) (div_pos he (by positivity)))
  refine ⟨L,fun T hT => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (tsum_nonneg (fun _ => abs_nonneg _))]
  refine (hL T hT).2.trans_lt ?_
  have heq : ε/(2*A)*A=ε/2 := by field_simp; ring
  rw [heq]; linarith only [he]

/-- A single mask on the logarithmic shells has limiting mass equal to
its geometric series. The mask may include negative signs. -/
theorem critical_shell_reading {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {b u v : ℝ} (hb : 1<b) (hu : 0<u) (huv : u≤v) (w : ℕ → ℝ) (hw : ∀ n, |w n|≤1) :
    Tendsto (fun T : ℝ => ∑' n : ℕ, w n*(T*ordinateBand F b u v T n)) atTop
      (𝓝 (ordinateCuspConstant W F*(u⁻¹-v⁻¹)*(∑' n : ℕ,w n*(b⁻¹)^n))) := by
  let A := ordinateCuspConstant W F*(u⁻¹-v⁻¹)
  let g := fun n : ℕ => (b⁻¹)^n
  let V := fun (T : ℝ) (n : ℕ) => T*ordinateBand F b u v T n
  have herr := critical_shell_total_variation hW ht hF hf hb hu huv
  have hq : 0≤b⁻¹ := inv_nonneg.mpr (zero_le_one.trans hb.le)
  have hg : Summable g := summable_geometric_of_lt_one hq ((inv_lt_one₀ (zero_lt_one.trans hb)).mpr hb)
  have wm : Summable (fun n => w n*g n) := by
    apply hg.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hq n)]
    exact mul_le_of_le_one_left (pow_nonneg hq n) (hw n)
  have heq : A*(∑' n,w n*g n)=∑' n,w n*(A*g n) := by
    rw [←tsum_mul_left]
    exact tsum_congr fun n => by ring
  change Tendsto (fun T => ∑' n,w n*V T n) atTop (𝓝 (A*(∑' n,w n*g n)))
  rw [heq]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have lim := herr.2.eventually_lt_const hε
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (herr.1.and lim)
  refine ⟨T₀,fun T ht' => ?_⟩
  let err := fun n => w n*(V T n-A*g n)
  have hdom (n : ℕ) : ‖err n‖ ≤ |V T n-A*g n| := by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hw n)
  have hd : Summable err := (hT T ht').1.of_norm_bounded hdom
  have hbase : Summable (fun n => w n*(A*g n)) :=
    (wm.mul_left A).congr (fun n => by ring)
  have hv : Summable (fun n => w n*V T n) := (hd.add hbase).congr (fun n => by dsimp [err]; ring)
  rw [Real.dist_eq,←hv.tsum_sub hbase]
  have hsum : (∑' n, (w n*V T n-w n*(A*g n)))=∑' n,err n := tsum_congr (fun n => by dsimp [err]; ring)
  rw [hsum,←Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hd.norm).trans_lt ((hd.norm.tsum_le_tsum hdom (hT T ht').1).trans_lt (hT T ht').2)

/-- The even and odd dyadic octaves divide the full cusp coefficient
in the ratio two to one. Taking b=4 selects each parity without an
oscillatory subtraction. -/
theorem alternating_dyadic_octaves {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun T : ℝ => T*∑' n : ℕ,ordinateBand F 4 1 2 T n) atTop (𝓝 (2*ordinateCuspConstant W F/3)) ∧
    Tendsto (fun T : ℝ => T*∑' n : ℕ,ordinateBand F 4 2 4 T n) atTop (𝓝 (ordinateCuspConstant W F/3)) := by
  have read (u v : ℝ) (hu : 0<u) (huv : u≤v) := critical_shell_reading hW ht hF hf
    (b := 4) (by norm_num) hu huv (fun _ => 1) (fun _ => by norm_num)
  have hseries : (∑' n : ℕ, ((4:ℝ)⁻¹)^n)=4/3 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  constructor
  · have h := read 1 2 (by norm_num) (by norm_num)
    simp only [one_mul,tsum_mul_left,hseries] at h
    convert h using 2 <;> ring
  · have h := read 2 4 (by norm_num) (by norm_num)
    simp only [one_mul,tsum_mul_left,hseries] at h
    convert h using 2 <;> ring

private theorem wall_coefficient_pos {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W F) : 0 < ordinateCuspConstant W F := by
  have he : (∫ u : ℝ,F u^2*Real.exp (-(8*u)))=criticalHalfLineExponentialPair F F := by
    unfold criticalHalfLineExponentialPair
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  have hpos := exponentialPair_self_pos (criticalHalfLineEnergyDomain_of_groundState hF)
    (isConfinedNullVector_of_groundState hW ht hF).2.1
  exact div_pos (mul_pos (mul_pos (by norm_num) (criticalAliasCoefficient_positive hW)) (he ▸ hpos))
    Real.pi_pos

/-- A bounded signed mask detects the finite-layer obstruction exactly
when its geometric series is nonzero. For a mask of zero geometric
mean the measured tail tends to zero for every admissible ground state. -/
theorem sequential_shell_vanishing_iff {b u v : ℝ} (hb : 1<b) (hu : 0<u) (huv : u<v)
    (w : ℕ → ℝ) (hw : ∀ n, |w n|≤1) :
    (BacklundConverse.FiniteOffLine →
      ∀ W (F : ℝ → ℝ), 0<W → (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal) →
        IsCriticalHalfLineGroundState W F →
        ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
          Tendsto (fun k => ∑' n : ℕ,w n*(t k*ordinateBand F b u v (t k) n)) atTop (𝓝 0)) ↔
      (∑' n : ℕ,w n*(b⁻¹)^n)=0 ∨ (BacklundConverse.FiniteOffLine → RiemannHypothesis) := by
  have hn := zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis.symm.trans
    zetaBeyondTheWallPrimeContinuation_iff_no_criticalState
  constructor
  · intro h
    by_cases hz : (∑' n : ℕ,w n*(b⁻¹)^n)=0
    · exact Or.inl hz
    refine Or.inr fun hf => hn.mpr ?_
    rintro ⟨W,F,hW,ht,hF⟩
    obtain ⟨t,htop,hzero⟩ := h hf W F hW ht hF
    have hlim := (critical_shell_reading hW ht hF hf hb hu huv.le w hw).comp htop
    have hcoef := wall_coefficient_pos hW ht hF
    have hdiff : 0<u⁻¹-v⁻¹ := sub_pos.mpr (inv_lt_inv₀ (hu.trans huv) hu |>.mpr huv)
    exact (mul_ne_zero (mul_pos hcoef hdiff).ne' hz) (tendsto_nhds_unique hlim hzero)
  · rintro (hz | h) hf W F hW ht hF
    · refine ⟨fun n => n,tendsto_natCast_atTop_atTop,?_⟩
      have hlim := (critical_shell_reading hW ht hF hf hb hu huv.le w hw).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [Function.comp_apply,hz,mul_zero] using hlim
    · exact ((hn.mp (h hf)) ⟨W,F,hW,ht,hF⟩).elim


end GaloisForLFunctions.ExclusionOfTheCriticalState
