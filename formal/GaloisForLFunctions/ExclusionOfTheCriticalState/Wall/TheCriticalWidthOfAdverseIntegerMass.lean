import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheIntegerWaveHasVanishingMeanAbsoluteError
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheSignOfTheStateAtTheWallIsTheSignOfItsHalfCharge
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoBoundaryLaplaceZero

/-!
# The adverse integer mass next to the wall

For the critical profile, the real Laplace charge fixes the sign at its terminal
edge. In the first H integers above exp(t), the negative coefficient mass has
order H/√(exp(t)t) over a growing range of H. Its upper bound counts all unit
references. Its lower bound counts the multiples of six in the outer half.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The charge at zero and the charge at one half have the same sign. -/
private theorem integral_mul_halfCharge_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 < (∫ u, F u) * (negativeHalfLineLaplace (cx F) (1/2)).re := by
  let L := fun x : ℝ => (negativeHalfLineLaplace (cx F) (x : ℂ)).re
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hc : ContinuousOn L (Icc 0 (1/2)) := by
    intro x hx
    have h := differentiableAt_laplace_of_sq hd hd.exponential (w := (x : ℂ))
      (by simp only [Complex.ofReal_re]; linarith only [hx.1])
    exact (Complex.continuous_re.continuousAt.comp
      (h.continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hn (x : ℝ) (hx : x ∈ Icc 0 (1/2)) : L x ≠ 0 := by
    intro hz
    apply criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF
      (show 0 ≤ (x : ℂ).re from hx.1)
    dsimp only [L] at hz
    rw [negativeHalfLineLaplace_ofReal, Complex.ofReal_re] at hz
    rw [negativeHalfLineLaplace_ofReal, hz, Complex.ofReal_zero]
  have h := _root_.HTGeometry.mul_pos_of_ne_zero_on_Icc (by norm_num : (0:ℝ) ≤ 1/2) hc hn
  have hzero : L 0 = ∫ u, F u := by
    simp only [L, negativeHalfLineLaplace_ofReal, Complex.ofReal_re, zero_mul, Real.exp_zero, mul_one]
  rw [hzero] at h
  simpa only [L, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h

/-- Multiplication by the total charge fixes the orientation of the pointwise
wall law. Its limiting coefficient is positive for either normalization. -/
theorem criticalState_oriented_wall_limit {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    let m := ∫ u, Φ u
    let L := |m| *Real.sqrt (8*criticalAliasCoefficient W₀*∫ u : ℝ, F u^2*Real.exp (-(8*u)))
    0 < L ∧ Tendsto (fun k : ℝ => (m*Φ (-k))*Real.sqrt (Real.log (1/k))) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨s,hs,Ψ,hΨ,heΨ,_,_,hlaw,_,δ,hδ,hsgn⟩ :=
    criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let m := ∫ u, Φ u
  let q := (negativeHalfLineLaplace (cx F) (1/2)).re
  have hmq : 0 < m*q := by
    dsimp only [m,q]
    rw [← integral_congr_ae he]
    exact integral_mul_halfCharge_pos hW ht hF
  have hterm := criticalState_eventually_halfCharge_mul_terminalMass_pos hW ht hF
  have hnear : ∀ᶠ k : ℝ in 𝓝[>] 0, k ∈ Ioo 0 δ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨δ,hδ,subset_rfl⟩
  obtain ⟨k,hk,hkq⟩ := (hnear.and hterm).exists
  let J := ∫ u in Ioo (-k) 0, Φ u
  have hqJ : 0 < q*J := by
    simpa only [q,J,integral_congr_ae (ae_restrict_of_ae he)] using hkq.1
  have hsJ : 0 ≤ s*J := by
    dsimp only [J]
    rw [← integral_const_mul]
    apply setIntegral_nonneg measurableSet_Ioo
    intro u hu
    have h := hsgn (-u) ⟨neg_pos.mpr hu.2, by linarith only [hk.2,hu.1]⟩
    simpa only [neg_neg] using h.le
  have hmJ : 0 < m*J := by
    rcases mul_pos_iff.mp hmq with h | h <;>
      rcases mul_pos_iff.mp hqJ with h' | h' <;> first
      | exact mul_pos h.1 h'.2
      | exact mul_pos_of_neg_of_neg h.1 h'.2
      | linarith only [h.2,h'.1]
  have hms : 0 < m*s := by
    rcases hs with h | h <;> subst s
    · simp only [one_mul] at hsJ
      rw [mul_one]
      exact (mul_pos_iff.mp hmJ).elim (·.1) (fun z => (not_lt_of_ge hsJ z.2).elim)
    · simp only [neg_one_mul,neg_nonneg] at hsJ
      rw [mul_neg_one,neg_pos]
      exact (mul_pos_iff.mp hmJ).elim (fun z => (not_lt_of_ge hsJ z.2).elim) (·.1)
  have habs : m*s = |m| := by
    rcases hs with h | h <;> subst s
    · simp only [mul_one] at hms ⊢
      exact (abs_of_pos hms).symm
    · simp only [mul_neg_one,neg_pos] at hms ⊢
      exact (abs_of_neg hms).symm
  let Q := 8*criticalAliasCoefficient W₀*∫ u : ℝ, F u^2*Real.exp (-(8*u))
  have hQ : 0 < Q := mul_pos (mul_pos (by norm_num) (criticalAliasCoefficient_positive hW))
    (criticalState_exponentialMass_pos hW hF)
  change 0 < |m| *Real.sqrt Q ∧ Tendsto (fun k : ℝ => (m*Φ (-k))*Real.sqrt (Real.log (1/k)))
    (𝓝[>] 0) (𝓝 (|m| *Real.sqrt Q))
  rw [← habs]
  refine ⟨mul_pos hms (Real.sqrt_pos.2 hQ),?_⟩
  simpa only [Q,mul_assoc] using hlaw.const_mul m

private theorem criticalState_oriented_wall_bound {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 < δ ∧ ∀ k ∈ Ioo 0 δ,
      0 < (∫ u, Φ u)*Φ (-k) ∧ c ≤ ((∫ u, Φ u)*Φ (-k))*Real.sqrt (Real.log (1/k)) ∧
        ((∫ u, Φ u)*Φ (-k))*Real.sqrt (Real.log (1/k)) ≤ C := by
  let L := |∫ u, Φ u| *Real.sqrt (8*criticalAliasCoefficient W₀*∫ u : ℝ, F u^2*Real.exp (-(8*u)))
  obtain ⟨hL,hlim⟩ := criticalState_oriented_wall_limit hW ht hF hc he
  change 0 < L at hL
  have hbounds := (hlim.eventually_const_lt (by linarith only [hL] : L/2 < L)).and
    (hlim.eventually_lt_const (by linarith only [hL] : L < 2*L))
  obtain ⟨δ,hδ,hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbounds
  refine ⟨L/2,2*L,δ,by positivity,by positivity,hδ,fun k hk => ?_⟩
  have h := hb hk
  have hp := (show 0 < L/2 by positivity).trans h.1
  exact ⟨pos_of_mul_pos_left hp (Real.sqrt_nonneg _),h.1.le,h.2.le⟩

/-- The integers in the first H units after exp(t). -/
def wallIntegerWindow (t H : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊Real.exp t⌋₊ ⌊Real.exp t+H⌋₊

/-- Adverse coefficient mass of a selected finite set before time averaging. -/
def adverseIntegerMass (Φ : ℝ → ℝ) (t : ℝ) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, max (-((∫ u, Φ u)*((vonMangoldt n-1)*continuousIntegerAtom Φ n t))) 0

private theorem floor_window_endpoints {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) : x < n ∧ (n:ℝ) ≤ y := by
  obtain ⟨ha,hb⟩ := Finset.mem_Ioc.mp hn
  exact ⟨(Nat.floor_lt hx).mp ha,(Nat.le_floor_iff (hx.trans hxy)).mp hb⟩

private theorem card_floor_window {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y-x-1 ≤ ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ) ∧
      ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ) ≤ y-x+1 := by
  rw [Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono hxy)]
  constructor
  · linarith only [Nat.lt_floor_add_one y, Nat.floor_le hx]
  · linarith only [Nat.floor_le (hx.trans hxy),Nat.lt_floor_add_one x]

/-- All indices have logarithmic gap at most exp(−t/4). On the outer half the
gap is at least exp(−t), even when the wall is arbitrarily close to an integer. -/
private theorem window_log_gap {t H : ℝ} (ht : 0 ≤ t) (hH : 4 ≤ H)
    (hH' : H ≤ Real.exp (3*t/4)) {n : ℕ} (hn : n ∈ wallIntegerWindow t H) :
    let X := Real.exp t
    let k := Real.log n-t
    0 < k ∧ k ≤ Real.exp (-t/4) ∧ (X+H/2 < n → Real.exp (-t) ≤ k) := by
  let X := Real.exp t
  have hX : 0 < X := Real.exp_pos _
  have hHX : H ≤ X := hH'.trans (Real.exp_le_exp.2 (by linarith only [ht]))
  obtain ⟨ha,hb⟩ := floor_window_endpoints hX.le
    (by dsimp only [X]; linarith only [hH] : X ≤ X+H) hn
  have hn0 := hX.trans ha
  have hprod : X*Real.exp (-t/4) = Real.exp (3*t/4) := by
    dsimp only [X]; rw [← Real.exp_add]; congr 1; ring
  have hle : (n:ℝ) ≤ Real.exp (t+Real.exp (-t/4)) := by
    rw [Real.exp_add]
    calc (n:ℝ) ≤ X*(Real.exp (-t/4)+1) := by rw [mul_add,hprod,mul_one]; linarith only [hb,hH']
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hX.le
  refine ⟨sub_pos.mpr ((Real.lt_log_iff_exp_lt hn0).mpr ha),
    sub_le_iff_le_add'.mpr ((Real.log_le_iff_le_exp hn0).mpr hle),fun hm => ?_⟩
  have hk := Real.log_le_sub_one_of_pos (div_pos hX hn0)
  rw [Real.log_div hX.ne' hn0.ne',show Real.log X=t from Real.log_exp t] at hk
  have hnX : (n:ℝ) ≤ 2*X := by linarith only [hb,hHX]
  have hd : 2 ≤ (n:ℝ)-X := by linarith only [hm,hH]
  have hlow : 1/X ≤ 1-X/(n:ℝ) := by
    rw [one_sub_div hn0.ne',div_le_div_iff₀ hX hn0,one_mul]
    exact hnX.trans (mul_le_mul_of_nonneg_right hd hX.le)
  change Real.exp (-t) ≤ Real.log n-t
  rw [Real.exp_neg,← one_div]
  exact hlow.trans (by linarith only [hk])

private theorem no_mangoldt_on_sixes (j : ℕ) : vonMangoldt (6*j) = 0 := by
  rcases j with _ | j
  · simp
  apply vonMangoldt_eq_zero_iff.mpr
  rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le (by omega : 2 ≤ 6*(j+1))]
  refine ⟨2,Nat.mem_primeFactors.mpr ⟨Nat.prime_two,?_,by omega⟩,
    3,Nat.mem_primeFactors.mpr ⟨Nat.prime_three,?_,by omega⟩,by norm_num⟩
  · exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) _
  · exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) _

/-- The terminal wall law fixes the critical width for adverse mass. Uniformly
from width 24 through exp(3t/4), the full negative coefficient mass has order
H/(exp(t/2) sqrt(t)). The upper estimate holds after any selection of indices. -/
theorem criticalState_adverse_mass_by_width {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ t : ℝ in atTop, ∀ H : ℝ, 24 ≤ H →
      H ≤ Real.exp (3*t/4) →
      c*H/(Real.exp (t/2)*Real.sqrt t) ≤ adverseIntegerMass Φ t (wallIntegerWindow t H) ∧
      ∀ A ⊆ wallIntegerWindow t H, adverseIntegerMass Φ t A ≤ C*H/(Real.exp (t/2)*Real.sqrt t) := by
  obtain ⟨c,C,δ,hc0,hC,hδ,hlaw⟩ := criticalState_oriented_wall_bound hW ht hF hc he
  have hl : Tendsto (fun t : ℝ => Real.exp (-t/4)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/4:ℝ)<0))
    exact h.congr fun t => congrArg Real.exp (show (-1/4:ℝ)*t = -t/4 by ring)
  refine ⟨c/48,4*C,by positivity,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),hl.eventually_lt_const hδ] with t ht0 hδt
  intro H hH hH'
  let X := Real.exp t
  let R := Real.exp (t/2)
  let m := ∫ u, Φ u
  let a := fun n : ℕ => max (-(m*((vonMangoldt n-1)*continuousIntegerAtom Φ n t))) 0
  have hX : 0 < X := Real.exp_pos _
  have hR : 0 < R := Real.exp_pos _
  have hR2 : R^2=X := by dsimp only [R,X]; rw [sq,← Real.exp_add]; congr 1; ring
  have hH0 : 0 < H := by linarith only [hH]
  have hHX : H ≤ X := hH'.trans (Real.exp_le_exp.2 (by linarith only [ht0]))
  have hs := Real.sqrt_pos.2 ht0
  have hloc (n : ℕ) (hn : n ∈ wallIntegerWindow t H) :
      a n ≤ (2*C)/(R*Real.sqrt t) ∧
      (X+H/2 < n → vonMangoldt n=0 → c/(2*R*Real.sqrt t) ≤ a n) := by
    let k := Real.log n-t
    obtain ⟨hk,hk',houter⟩ := window_log_gap ht0.le (by linarith only [hH]) hH' hn
    obtain ⟨hp,hwlow,hw⟩ := hlaw k ⟨hk,hk'.trans_lt hδt⟩
    change 0 < m*Φ (-k) at hp
    change c ≤ (m*Φ (-k))*Real.sqrt (Real.log (1/k)) at hwlow
    change (m*Φ (-k))*Real.sqrt (Real.log (1/k)) ≤ C at hw
    obtain ⟨hxn,hnx⟩ := floor_window_endpoints hX.le (le_add_of_nonneg_right hH0.le) hn
    have hn0 := hX.trans hxn
    have hrn := Real.sqrt_pos.mpr hn0
    have hroot : R ≤ Real.sqrt n := by
      rw [← Real.sqrt_sq hR.le]; exact Real.sqrt_le_sqrt (hR2 ▸ hxn.le)
    have hroot' : Real.sqrt n ≤ 2*R := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2*R)]
      apply Real.sqrt_le_sqrt
      nlinarith only [hR2,hHX,hnx,hX.le]
    have hlog : t/4 ≤ Real.log (1/k) := by
      rw [one_div,Real.log_inv]
      have hkle := Real.log_le_log hk hk'
      rw [Real.log_exp] at hkle
      linarith only [hkle]
    have hsq : Real.sqrt t ≤ 2*Real.sqrt (Real.log (1/k)) := by
      calc _ ≤ Real.sqrt (4*Real.log (1/k)) := Real.sqrt_le_sqrt (by linarith only [hlog])
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
    let v := (Real.sqrt n)⁻¹*(m*Φ (-k))
    have hv : 0 ≤ v := mul_nonneg (inv_nonneg.mpr hrn.le) hp.le
    have heqn : a n = max (-((vonMangoldt n-1)*v)) 0 := by
      dsimp only [a,v,continuousIntegerAtom,k]; rw [neg_sub]; congr 2; ring
    rw [heqn]
    constructor
    · have hprof : m*Φ (-k) ≤ 2*C/Real.sqrt t := by
        apply (le_div_iff₀ hs).2
        calc _ ≤ (m*Φ (-k))*(2*Real.sqrt (Real.log (1/k))) := mul_le_mul_of_nonneg_left hsq hp.le
          _ ≤ _ := by linarith only [hw]
      have hwt : v ≤ 2*C/(R*Real.sqrt t) := by
        calc v ≤ R⁻¹*(2*C/Real.sqrt t) := mul_le_mul
               ((inv_le_inv₀ hrn hR).2 hroot) hprof hp.le (inv_nonneg.mpr hR.le)
          _ = _ := by field_simp [hR.ne',hs.ne']
      exact max_le (by linarith only [mul_nonneg (vonMangoldt_nonneg (n := n)) hv,hwt])
        (div_nonneg (by positivity) (mul_nonneg hR.le hs.le))
    · intro ho hzero
      rw [hzero,zero_sub,neg_one_mul,neg_neg,max_eq_left hv]
      have hklo := houter ho
      have hlg := Real.log_le_log (Real.exp_pos _) hklo
      rw [Real.log_exp] at hlg
      have hsl : Real.sqrt (Real.log (1/k)) ≤ Real.sqrt t := by
        apply Real.sqrt_le_sqrt; rw [one_div,Real.log_inv]; linarith only [hlg]
      have hw' := hwlow.trans (mul_le_mul_of_nonneg_left hsl hp.le)
      have hφ : c/Real.sqrt t ≤ m*Φ (-k) := (div_le_iff₀ hs).2 hw'
      calc c/(2*R*Real.sqrt t) = (2*R)⁻¹*(c/Real.sqrt t) := by field_simp [hR.ne',hs.ne']
        _ ≤ v := mul_le_mul ((inv_le_inv₀ (by positivity : 0 < 2*R) hrn).2 hroot') hφ
                   (div_nonneg hc0.le hs.le) (inv_nonneg.mpr hrn.le)
  constructor
  · let D := Finset.Ioc ⌊(X+H/2)/6⌋₊ ⌊(X+H)/6⌋₊
    have hd0 : 0 ≤ (X+H/2)/6 := by positivity
    have hdd : (X+H/2)/6 ≤ (X+H)/6 := by linarith only [hH0]
    have hcard : H/24 ≤ (D.card : ℝ) := by
      linarith only [(card_floor_window hd0 hdd).1,hH]
    have hd (j : ℕ) (hj : j ∈ D) :
        6*j ∈ wallIntegerWindow t H ∧ X+H/2 < ((6*j:ℕ):ℝ) := by
      obtain ⟨hlo,hhi⟩ := floor_window_endpoints hd0 hdd hj
      have hj0 : X+H/2 < ((6*j:ℕ):ℝ) := by push_cast; linarith only [hlo]
      refine ⟨Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hX.le).2 (by linarith only [hj0,hH0]),Nat.le_floor ?_⟩,hj0⟩
      push_cast; linarith only [hhi]
    have hsub : D.image (6*·) ⊆ wallIntegerWindow t H := by
      intro n hn; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn; exact (hd j hj).1
    let b := c/(2*R*Real.sqrt t)
    have hb : 0 ≤ b := by dsimp only [b]; positivity
    have hinj : Function.Injective (fun j : ℕ => 6*j) := fun i j h => by
      change 6*i = 6*j at h
      omega
    change (c/48)*H/(R*Real.sqrt t) ≤ ∑ n ∈ wallIntegerWindow t H, a n
    calc _ = (H/24)*b := by dsimp only [b]; field_simp [hR.ne',hs.ne']; ring
      _ ≤ (D.card : ℝ)*b := mul_le_mul_of_nonneg_right hcard hb
      _ = ∑ _j ∈ D, b := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ j ∈ D, a (6*j) := Finset.sum_le_sum fun j hj =>
            (hloc _ (hd j hj).1).2 (hd j hj).2 (no_mangoldt_on_sixes j)
      _ = ∑ n ∈ D.image (6*·), a n := (Finset.sum_image (fun _ _ _ _ h => hinj h)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => le_max_right _ _
  · intro A hA
    let b := 2*C/(R*Real.sqrt t)
    have hb : 0 ≤ b := by dsimp only [b]; positivity
    have hcard : (A.card:ℝ) ≤ 2*H := by
      have hle : (A.card:ℝ) ≤ (wallIntegerWindow t H).card := by exact_mod_cast Finset.card_le_card hA
      have hn := (card_floor_window hX.le (le_add_of_nonneg_right hH0.le)).2
      change ((wallIntegerWindow t H).card : ℝ) ≤ X+H-X+1 at hn
      linarith only [hle,hn,hH]
    change ∑ n ∈ A, a n ≤ 4*C*H/(R*Real.sqrt t)
    calc _ ≤ ∑ _n ∈ A, b := Finset.sum_le_sum fun n hn => (hloc n (hA hn)).1
      _ = (A.card:ℝ)*b := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (2*H)*b := mul_le_mul_of_nonneg_right hcard hb
      _ = _ := by dsimp only [b]; field_simp [hR.ne',hs.ne']; ring

/-- Critical-width adverse mass stays between two positive constants. For every
selection in the full range, deleting the selected atoms retains the entire
complement and its square charge, with the indicated one-sided cost. -/
theorem riemannHypothesis_or_critical_width_adverse_mass : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (c C : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ᶠ t : ℝ in atTop,
        let R := Real.exp (t/2)*Real.sqrt t
        let m := ∫ u, Φ u
        let v := fun n : ℕ => (vonMangoldt n-1)*continuousIntegerAtom Φ n t
        (c ≤ adverseIntegerMass Φ t (wallIntegerWindow t R) ∧
          adverseIntegerMass Φ t (wallIntegerWindow t R) ≤ C) ∧
        ∀ H : ℝ, 24 ≤ H → H ≤ Real.exp (3*t/4) →
          c*H/R ≤ adverseIntegerMass Φ t (wallIntegerWindow t H) ∧
          ∀ A ⊆ wallIntegerWindow t H, adverseIntegerMass Φ t A ≤ C*H/R ∧
            m*((∑' n : {j : ℕ // j ∉ A}, v n)-m/2)-C*H/R ≤ m*((∑' n : ℕ, v n)-m/2) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,⟨D,_,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨c,C,hc0,hC,hbnd⟩ := criticalState_adverse_mass_by_width hW ht hF hc he
  refine Or.inr ⟨W₀,F,Φ,c,C,hW,ht,hF,hc,he,hc0,hC,?_⟩
  filter_upwards [hbnd,eventually_ge_atTop (46:ℝ)] with t h ht46
  let R := Real.exp (t/2)*Real.sqrt t
  let v := fun n : ℕ => (vonMangoldt n-1)*continuousIntegerAtom Φ n t
  let m := ∫ u, Φ u
  have ht0 : 0 < t := by linarith only [ht46]
  have hR : 0 < R := mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 ht0)
  have h1 : 1 ≤ Real.sqrt t := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by linarith only [ht46] : 1 ≤ t)
  have hlow : 24 ≤ R := (by linarith only [Real.add_one_le_exp (t/2),ht46] : 24 ≤ Real.exp (t/2)).trans
    (le_mul_of_one_le_right (Real.exp_pos _).le h1)
  have hu : Real.sqrt t ≤ Real.exp (t/4) := by
    have he : 0 ≤ 1+t/4 := by linarith only [ht0]
    have hx : t ≤ (1+t/4)^2 := by nlinarith only [sq_nonneg (1-t/4)]
    calc _ ≤ Real.sqrt ((1+t/4)^2) := Real.sqrt_le_sqrt hx
      _ = 1+t/4 := Real.sqrt_sq he
      _ ≤ _ := by linarith only [Real.add_one_le_exp (t/4)]
  have hhigh : R ≤ Real.exp (3*t/4) := by
    calc R ≤ Real.exp (t/2)*Real.exp (t/4) := mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨hcrit,hsel⟩ := h R hlow hhigh
  have hcrt := hsel _ (Finset.Subset.refl _)
  change c*R/R ≤ _ at hcrit
  change _ ≤ C*R/R at hcrt
  rw [mul_div_cancel_right₀ _ hR.ne'] at hcrit hcrt
  refine ⟨⟨hcrit,hcrt⟩,fun H hH hH' => ⟨(h H hH hH').1,fun A hA => ⟨(h H hH hH').2 _ hA,?_⟩⟩⟩
  have hsum : Summable v := ((summable_mangoldt_integerAtom hb t).sub
    (summable_continuousIntegerAtom hb t)).congr fun n => by simp only [v,sub_mul,one_mul]
  have hneg : -(m*(∑ n ∈ A, v n)) ≤ adverseIntegerMass Φ t A := by
    rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun n _ => le_max_left _ _
  change m*((∑' n : {j : ℕ // j ∉ A}, v n)-m/2)-C*H/R ≤ m*((∑' n, v n)-m/2)
  rw [← hsum.sum_add_tsum_compl (s := A)]
  change m*((∑' n : {j : ℕ // j ∉ A}, v n)-m/2)-C*H/R ≤
    m*((∑ n ∈ A, v n)+(∑' n : {j : ℕ // j ∉ A}, v n)-m/2)
  linarith only [hneg.trans ((h H hH hH').2 _ hA)]

#print axioms riemannHypothesis_or_critical_width_adverse_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
