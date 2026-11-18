import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheCriticalWidthOfAdverseIntegerMass
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheMangoldtMassInPowerWidthIntervals
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheRemoteVariationOfTheStateWeights
import GaloisForLFunctions.RHTower.FreeLagSymbolBoundaryLayer

/-!
# The signed Chebyshev reading at the critical width

The ground-state wall weight is nearly constant on each fixed outer fraction
of the interval. A uniform Mangoldt bound pays for the inner fraction before
it tends to zero. Thus the signed source on this interval retains the actual
short-interval Chebyshev excess.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- First width for which the adverse wall mass stays of positive order. -/
def criticalWallWidth (t : ℝ) := Real.exp (t/2)*Real.sqrt t

private theorem sqrt_time_le_exp_quarter {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt t ≤ Real.exp (t/4) := by
  have ha : 0 ≤ 1+t/4 := by linarith only [ht]
  calc _ ≤ Real.sqrt ((1+t/4)^2) := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (1-t/4)])
    _ = 1+t/4 := Real.sqrt_sq ha
    _ ≤ _ := by linarith only [Real.add_one_le_exp (t/4)]

/-- Throughout any fixed outer fraction of the critical interval, the
normalized state atom converges to the same constant. The fraction may vary
with the sample, so the limit is uniform away from the left endpoint. -/
private theorem scaled_wall_atom {ι : Type*} {f : Filter ι} {t d : ι → ℝ}
    (ht : Tendsto t f atTop) {η B : ℝ} (hη : 0 < η) (hB : 0 < B) (hd : ∀ᶠ i in f, d i ∈ Icc η B)
    {Φ : ℝ → ℝ} {m L : ℝ} (hw : Tendsto (fun k : ℝ => (m*Φ (-k))*Real.sqrt (Real.log (1/k)))
      (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun i => criticalWallWidth (t i) * (m*continuousIntegerAtom Φ
      (Real.exp (t i)+d i*criticalWallWidth (t i)) (t i))) f (𝓝 (Real.sqrt 2*L)) := by
  let v := fun i => Real.exp (-(t i)/2)*Real.sqrt (t i)
  let q := fun i => 1+d i*v i
  let k := fun i => Real.log (q i)
  let l := fun i => Real.log (1/k i)
  have ht0 := ht.eventually_gt_atTop 0
  have hv0 : Tendsto v f (𝓝 0) := by
    have hexp : Tendsto (fun i => Real.exp (-(t i)/4)) f (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (by norm_num : (-1/4:ℝ)<0))
      exact h.congr fun i => congrArg Real.exp (show (-1/4:ℝ)*t i = -(t i)/4 by ring)
    refine squeeze_zero' (Eventually.of_forall fun i => mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) ?_ hexp
    filter_upwards [ht0] with i hi
    calc v i ≤ Real.exp (-(t i)/2)*Real.exp (t i/4) :=
          mul_le_mul_of_nonneg_left (sqrt_time_le_exp_quarter hi.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hBv : Tendsto (fun i => B*v i) f (𝓝 0) := by
    simpa only [mul_zero] using hv0.const_mul B
  have hq0 : Tendsto q f (𝓝 1) := by
    have hz : Tendsto (fun i => d i*v i) f (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hBv
      · filter_upwards [hd] with i hi
        exact mul_nonneg (hη.le.trans hi.1) (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
      · filter_upwards [hd] with i hi
        exact mul_le_mul_of_nonneg_right hi.2 (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    simpa only [add_zero] using hz.const_add 1
  have hgeo : ∀ᶠ i in f, 0 < v i ∧ 1 < q i ∧ 0 < k i ∧ η/2*v i ≤ k i ∧ k i ≤ B*v i := by
    filter_upwards [ht0,hd,hBv.eventually_lt_const zero_lt_one] with i hi hdi hv
    have hvpos : 0 < v i := mul_pos (Real.exp_pos _) (Real.sqrt_pos.mpr hi)
    have hprod := mul_pos (hη.trans_le hdi.1) hvpos
    have hq : 1 < q i := by dsimp only [q]; linarith only [hprod]
    have hq2 : q i ≤ 2 := by
      dsimp only [q]; linarith only [mul_le_mul_of_nonneg_right hdi.2 hvpos.le,hv]
    have hqpos := zero_lt_one.trans hq
    have hlo := Real.log_le_sub_one_of_pos (inv_pos.mpr hqpos)
    rw [Real.log_inv] at hlo
    have hlow : η/2*v i ≤ 1-(q i)⁻¹ := by
      rw [← one_div,one_sub_div hqpos.ne',le_div_iff₀ hqpos]
      calc (η/2*v i)*q i ≤ (η/2*v i)*2 := mul_le_mul_of_nonneg_left hq2 (by positivity)
        _ = η*v i := by ring
        _ ≤ d i*v i := mul_le_mul_of_nonneg_right hdi.1 hvpos.le
        _ = q i-1 := by dsimp only [q]; ring
    refine ⟨hvpos,hq,Real.log_pos hq,hlow.trans (by dsimp only [k]; linarith only [hlo]),?_⟩
    exact (Real.log_le_sub_one_of_pos hqpos).trans (by
      dsimp only [q]
      linarith only [mul_le_mul_of_nonneg_right hdi.2 hvpos.le])
  have hk0 : Tendsto k f (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨squeeze_zero' (hgeo.mono fun _ h => h.2.2.1.le) (hgeo.mono fun _ h => h.2.2.2.2) hBv,
      hgeo.mono fun _ h => h.2.2.1⟩
  have hlogv : Tendsto (fun i => -(Real.log (v i))/t i) f (𝓝 (1/2)) := by
    have hlog := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht).div_const 2
    have hlim := (tendsto_const_nhds (x := (1/2 : ℝ))).sub hlog
    rw [zero_div,sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [ht0] with i hi
    dsimp only [v,Function.comp_apply,id_eq]
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.sqrt_pos.mpr hi).ne',Real.log_exp,Real.log_sqrt hi.le]
    field_simp [hi.ne']; ring
  have hlogk : Tendsto (fun i => l i/t i) f (𝓝 (1/2)) := by
    have hsmall := (tendsto_const_nhds (x := Real.log (η/2))).div_atTop ht
    have hup := hlogv.sub hsmall
    rw [sub_zero] at hup
    have hlo := hlogv.sub ((tendsto_const_nhds (x := Real.log B)).div_atTop ht)
    rw [sub_zero] at hlo
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    · filter_upwards [ht0,hgeo] with i hi hg
      dsimp only [l]; rw [one_div,Real.log_inv]
      have h := Real.log_le_log hg.2.2.1 hg.2.2.2.2
      rw [Real.log_mul hB.ne' hg.1.ne'] at h
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith only [h]) hi.le
    · filter_upwards [ht0,hgeo] with i hi hg
      have hη2 : 0 < η/2 := by positivity
      have hx := Real.log_le_log (mul_pos hη2 hg.1) hg.2.2.2.1
      rw [Real.log_mul hη2.ne' hg.1.ne'] at hx
      dsimp only [l]; rw [one_div,Real.log_inv,← sub_div]
      exact div_le_div_of_nonneg_right (by linarith only [hx]) hi.le
  have hratio := (Real.continuous_sqrt.continuousAt.tendsto.comp hlogk).inv₀
    (by positivity : Real.sqrt (1/2:ℝ) ≠ 0)
  have hroot := (Real.continuous_sqrt.continuousAt.tendsto.comp hq0).inv₀
    (by norm_num : Real.sqrt (1:ℝ) ≠ 0)
  have hlim := (hratio.mul hroot).mul (hw.comp hk0)
  have hnum : (Real.sqrt (1/2:ℝ))⁻¹ = Real.sqrt 2 := by rw [one_div,Real.sqrt_inv,inv_inv]
  rw [hnum,Real.sqrt_one,inv_one,mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [ht0,hgeo,(hlogk.eventually_const_lt (by norm_num : (0:ℝ) < 1/2))] with i hi hg hlg
  have hlpos : 0 < l i := (div_pos_iff.mp hlg).elim (·.1) (fun h => (not_lt_of_ge hi.le h.2).elim)
  have hqpos := zero_lt_one.trans hg.2.1
  have hsample : Real.exp (t i)+d i*criticalWallWidth (t i)=Real.exp (t i)*q i := by
    have hprod : Real.exp (t i)*Real.exp (-(t i)/2)=Real.exp (t i/2) := by
      rw [← Real.exp_add]; congr 1; ring
    dsimp only [q,v,criticalWallWidth]; rw [← hprod]; ring
  have hgap : t i-Real.log (Real.exp (t i)*q i)= -(k i) := by
    dsimp only [k]; rw [Real.log_mul (Real.exp_pos _).ne' hqpos.ne',Real.log_exp]; ring
  dsimp only [Function.comp_apply]
  rw [hsample,continuousIntegerAtom,hgap,Real.sqrt_mul (Real.exp_pos _).le,← Real.exp_half,
    Real.sqrt_div hlpos.le]
  change ((Real.sqrt (l i)/Real.sqrt (t i))⁻¹*(Real.sqrt (q i))⁻¹)*
    ((m*Φ (-(k i)))*Real.sqrt (l i)) = (Real.exp (t i/2)*Real.sqrt (t i))*
      (m*((Real.exp (t i/2)*Real.sqrt (q i))⁻¹*Φ (-(k i))))
  field_simp [(Real.sqrt_pos.mpr hi).ne',(Real.sqrt_pos.mpr hlpos).ne',
    (Real.sqrt_pos.mpr hqpos).ne',(Real.exp_pos _).ne']

/-- Uniform form of the wall sample on the outer part of the interval. -/
theorem eventually_critical_band_wall_atom {Φ : ℝ → ℝ} {m L : ℝ}
    (hw : Tendsto (fun k : ℝ => (m*Φ (-k))*Real.sqrt (Real.log (1/k))) (𝓝[>] 0) (𝓝 L))
    {η B ε : ℝ} (hη : 0 < η) (hB : 0 < B) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ n : ℕ, Real.exp t+η*criticalWallWidth t < n →
      (n:ℝ) ≤ Real.exp t+B*criticalWallWidth t →
      |criticalWallWidth t*(m*continuousIntegerAtom Φ n t)-Real.sqrt 2*L| < ε := by
  let s : Set (ℝ×ℝ) := {p | p.2 ∈ Icc η B}
  let f := comap Prod.fst (atTop : Filter ℝ) ⊓ 𝓟 s
  have ht : Tendsto (fun p : ℝ×ℝ => p.1) f atTop := tendsto_comap.mono_left inf_le_left
  have hd : ∀ᶠ p : ℝ×ℝ in f, p.2 ∈ Icc η B :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ h => h)
  have hlim := scaled_wall_atom ht hη hB hd hw
  have h := hlim.eventually (Metric.ball_mem_nhds _ hε)
  have hue := eventually_comap.mp (eventually_inf_principal.mp h)
  filter_upwards [hue,eventually_gt_atTop (0:ℝ)] with t hut ht0
  intro n hlow hupp
  let H := criticalWallWidth t
  let d := ((n:ℝ)-Real.exp t)/H
  have hH : 0 < H := mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 ht0)
  have hdi : d ∈ Icc η B := ⟨(le_div_iff₀ hH).2 (by linarith only [hlow]),
    (div_le_iff₀ hH).2 (by linarith only [hupp])⟩
  have hr := hut (t,d) rfl hdi
  change dist (H*(m*continuousIntegerAtom Φ (Real.exp t+d*H) t)) (Real.sqrt 2*L) < ε at hr
  have hn : Real.exp t+d*H=n := by dsimp only [d]; field_simp [hH.ne']; ring
  simpa only [hn,Real.dist_eq] using hr

private theorem width_mangoldt_abs {C : ℝ}
    (ha : ∀ t : ℝ, 1 ≤ t → ∀ H : ℝ, Real.exp (t/4) ≤ H → H ≤ Real.exp t →
      ∑ n ∈ wallIntegerWindow t H, ArithmeticFunction.vonMangoldt n ≤ C*H)
    {t H : ℝ} (ht : 1 ≤ t) (hH : Real.exp (t/4) ≤ H) (hH' : H ≤ Real.exp t) :
    ∑ n ∈ wallIntegerWindow t H, |ArithmeticFunction.vonMangoldt n-1| ≤ (C+2)*H := by
  have hH1 : 1 ≤ H := (Real.one_le_exp (by linarith only [ht] : 0 ≤ t/4)).trans hH
  have hX := Real.exp_pos t
  have hn : ((wallIntegerWindow t H).card : ℝ) ≤ H+1 := by
    rw [wallIntegerWindow,Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono (by linarith only [hH1]))]
    linarith only [Nat.floor_le (by linarith only [hX,hH1] : 0 ≤ Real.exp t+H),Nat.lt_floor_add_one (Real.exp t)]
  calc _ ≤ ∑ n ∈ wallIntegerWindow t H, (ArithmeticFunction.vonMangoldt n+1) :=
             Finset.sum_le_sum fun n _ => (abs_sub _ _).trans_eq (by
               rw [abs_one,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg])
    _ ≤ _ := by
             rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
             linarith only [ha t ht H hH hH',hn,hH1]

/-- Separate the inner interval before replacing the state weight by its
limit on the outer interval. Both costs use the actual absolute coefficients. -/
private theorem sum_wall_weight_error {I J : Finset ℕ} (hIJ : I ⊆ J) {a w : ℕ → ℝ}
    {γ B ε : ℝ} (hε : 0 ≤ ε) (hinner : ∀ n ∈ I, |w n-γ| ≤ B)
    (houter : ∀ n ∈ J, n ∉ I → |w n-γ| ≤ ε) :
    |∑ n ∈ J, a n*(w n-γ)| ≤ B*(∑ n ∈ I, |a n|)+ε*(∑ n ∈ J, |a n|) := by
  have hi : |∑ n ∈ I, a n*(w n-γ)| ≤ B*∑ n ∈ I, |a n| := by
    rw [Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [abs_mul,mul_comm B]
    exact mul_le_mul_of_nonneg_left (hinner n hn) (abs_nonneg _)
  have ho : |∑ n ∈ J \ I, a n*(w n-γ)| ≤ ε*∑ n ∈ J, |a n| := by
    have hsum : ∑ n ∈ J \ I, |a n| ≤ ∑ n ∈ J, |a n| :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => abs_nonneg _
    apply le_trans _ (mul_le_mul_of_nonneg_left hsum hε)
    rw [Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [abs_mul,mul_comm ε]
    exact mul_le_mul_of_nonneg_left (houter n (Finset.mem_sdiff.mp hn).1 (Finset.mem_sdiff.mp hn).2)
      (abs_nonneg _)
  rw [← Finset.sum_sdiff hIJ]
  exact (abs_add_le _ _).trans <| (add_le_add ho hi).trans_eq (add_comm ..)

/-- Any fixed fraction of the critical width ultimately stays within the
linear sieve range. The whole width also stays below exp(3t/4). -/
private theorem criticalWallWidth_range {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1) :
    ∀ᶠ t : ℝ in atTop,
      0 < criticalWallWidth t ∧ Real.exp (t/4) ≤ η*criticalWallWidth t ∧
      η*criticalWallWidth t ≤ criticalWallWidth t ∧ criticalWallWidth t ≤ Real.exp (3*t/4) ∧
      Real.exp (3*t/4) ≤ Real.exp t := by
  have he : Tendsto (fun t : ℝ => Real.exp (t/4)) atTop atTop := by
    have h := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<1/4))
    exact h.congr fun t => congrArg Real.exp (show (1/4:ℝ)*t=t/4 by ring)
  filter_upwards [he.eventually_ge_atTop η⁻¹,eventually_ge_atTop (1:ℝ)] with t ht h1
  have ht0 := (by norm_num : (0:ℝ)<1).trans_le h1
  have hroot : 1 ≤ Real.sqrt t := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h1
  have he0 := Real.exp_pos (t/4)
  have hprod : Real.exp (t/4)*Real.exp (t/4)=Real.exp (t/2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hηmul : 1 ≤ η*Real.exp (t/4) := by
    simpa only [mul_inv_cancel₀ hη.ne'] using mul_le_mul_of_nonneg_left ht hη.le
  have hhalf : Real.exp (t/4) ≤ η*Real.exp (t/2) := by
    calc _ ≤ (η*Real.exp (t/4))*Real.exp (t/4) := le_mul_of_one_le_left he0.le hηmul
      _ = _ := by rw [mul_assoc,hprod]
  have hH : 0 < criticalWallWidth t := mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 ht0)
  refine ⟨hH,hhalf.trans ?_,mul_le_of_le_one_left hH.le hη',?_,Real.exp_le_exp.2 (by linarith only [ht0])⟩
  · dsimp only [criticalWallWidth]; rw [← mul_assoc]
    exact le_mul_of_one_le_right (mul_nonneg hη.le (Real.exp_pos _).le) hroot
  · calc _ ≤ Real.exp (t/2)*Real.exp (t/4) := mul_le_mul_of_nonneg_left (sqrt_time_le_exp_quarter ht0.le) (Real.exp_pos _).le
         _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem critical_width_atom_cap {Φ : ℝ → ℝ} {m L : ℝ}
    (hlaw : Tendsto (fun k : ℝ => (m*Φ (-k))*Real.sqrt (Real.log (1/k))) (𝓝[>] 0) (𝓝 L)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ t : ℝ in atTop, ∀ n ∈ wallIntegerWindow t (criticalWallWidth t),
      |criticalWallWidth t*(m*continuousIntegerAtom Φ n t)| ≤ B := by
  have hD := hlaw.abs.eventually_lt_const (lt_add_one |L|)
  obtain ⟨δ,hδ,hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hD
  have hl : Tendsto (fun t : ℝ => Real.exp (-t/4)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/4:ℝ)<0))
    exact h.congr fun t => congrArg Real.exp (show (-1/4:ℝ)*t = -t/4 by ring)
  refine ⟨2*(|L|+1),by positivity,?_⟩
  filter_upwards [criticalWallWidth_range (η := 1) zero_lt_one le_rfl, hl.eventually_lt_const hδ,
    eventually_ge_atTop (16:ℝ)] with t hr hδt ht
  intro n hn
  have ht0 : 0 < t := by linarith only [ht]
  have hx0 := Real.exp_pos t
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hn
  have ha := (Nat.floor_lt hx0.le).mp hlo
  have hh := (Nat.le_floor_iff (add_nonneg hx0.le hr.1.le)).mp hhi
  let k := Real.log n-t
  have hk : 0 < k := sub_pos.mpr ((Real.lt_log_iff_exp_lt (hx0.trans ha)).2 ha)
  have heq : Real.exp t*Real.exp (-t/4)=Real.exp (3*t/4) := by rw [← Real.exp_add]; congr 1; ring
  have hn' : (n:ℝ) ≤ Real.exp (t+Real.exp (-t/4)) := by
    rw [Real.exp_add]
    calc _ ≤ Real.exp t*(Real.exp (-t/4)+1) := by rw [mul_add,heq,mul_one]; linarith only [hh,hr.2.2.2.1]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hx0.le
  have hk' : k ≤ Real.exp (-t/4) := sub_le_iff_le_add'.2 ((Real.log_le_iff_le_exp (hx0.trans ha)).2 hn')
  have hwlt : |(m*Φ (-k))*Real.sqrt (Real.log (1/k))| < |L|+1 := hb ⟨hk,hk'.trans_lt hδt⟩
  have hw := hwlt.le
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at hw
  have hlog := Real.log_le_log hk hk'
  rw [Real.log_exp] at hlog
  have hs : Real.sqrt t ≤ 2*Real.sqrt (Real.log (1/k)) := by
    calc _ ≤ Real.sqrt (4*Real.log (1/k)) := Real.sqrt_le_sqrt (by rw [one_div,Real.log_inv]; linarith only [hlog])
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  have hR : Real.exp (t/2) ≤ Real.sqrt n := by
    rw [Real.exp_half]; exact Real.sqrt_le_sqrt ha.le
  have he : criticalWallWidth t*(m*continuousIntegerAtom Φ n t) =
      (Real.exp (t/2)/Real.sqrt n)*(m*Φ (-k))*Real.sqrt t := by
    dsimp only [criticalWallWidth,continuousIntegerAtom,k]; rw [neg_sub]; ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))]
  have hrel : Real.exp (t/2)/Real.sqrt n ≤ 1 := (div_le_one (Real.sqrt_pos.mpr (hx0.trans ha))).2 hR
  calc
    _ ≤ |m*Φ (-k)| *(2*Real.sqrt (Real.log (1/k))) := by
      exact mul_le_mul (mul_le_of_le_one_left (abs_nonneg _) hrel) hs (Real.sqrt_nonneg _) (abs_nonneg _)
    _ ≤ _ := by linarith only [hw]

/-- At the same width a Lipschitz profile vanishing at the wall has vanishing
adverse mass. Thus the positive lower bound for a critical state detects its
logarithmic edge singularity. -/
theorem lipschitz_adverse_critical_width_tendsto_zero {Φ : ℝ → ℝ} {K : NNReal}
    (hΦ : LipschitzWith K Φ) (h0 : Φ 0=0) :
    Tendsto (fun t : ℝ => adverseIntegerMass Φ t (wallIntegerWindow t (criticalWallWidth t)))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hM⟩ := mangoldt_mass_on_power_width
  let m := ∫ u, Φ u
  let D := (C+2)*|m| *(K:ℝ)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have he : Tendsto (fun t : ℝ => Real.exp (-t/4)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/4:ℝ)<0))
    exact h.congr fun t => congrArg Real.exp (show (-1/4:ℝ)*t = -t/4 by ring)
  have hlim := he.const_mul (4*D)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1:ℝ),criticalWallWidth_range (η := 1) zero_lt_one le_rfl] with t ht hr
  let X := Real.exp t
  let R := Real.exp (t/2)
  let H := criticalWallWidth t
  let J := wallIntegerWindow t H
  let B := |m| *(K:ℝ)*H/(X*R)
  have hX : 0 < X := Real.exp_pos _
  have hR : 0 < R := Real.exp_pos _
  have hH : 0 < H := hr.1
  have hHX : H ≤ X := hr.2.2.2.1.trans hr.2.2.2.2
  have hcost := width_mangoldt_abs hM ht (by simpa only [one_mul] using hr.2.1) hHX
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpt (n : ℕ) (hn : n ∈ J) :
      max (-(m*((ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t))) 0 ≤
        B*|ArithmeticFunction.vonMangoldt n-1| := by
    obtain ⟨hnl,hnu⟩ := Finset.mem_Ioc.mp hn
    have hlo := (Nat.floor_lt hX.le).1 hnl
    have hhi := (Nat.le_floor_iff (add_nonneg hX.le hH.le)).mp hnu
    have hn0 := hX.trans hlo
    have hk : 0 ≤ Real.log n-t := (sub_pos.mpr ((Real.lt_log_iff_exp_lt hn0).2 hlo)).le
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn0 hX)
    rw [Real.log_div hn0.ne' hX.ne',show Real.log X=t from Real.log_exp _] at hlog
    have hrange : Real.log n-t ≤ H/X := by
      apply hlog.trans
      rw [div_sub_one hX.ne']; exact div_le_div_of_nonneg_right (by linarith only [hhi]) hX.le
    have hp := hΦ.dist_le_mul (t-Real.log n) 0
    rw [h0,Real.dist_eq,sub_zero,Real.dist_eq,sub_zero,abs_of_nonpos (by linarith only [hk] : t-Real.log (n:ℝ) ≤ 0)] at hp
    have hφ : |Φ (t-Real.log n)| ≤ (K:ℝ)*(H/X) := hp.trans
      (mul_le_mul_of_nonneg_left (by linarith only [hrange]) K.coe_nonneg)
    have hroot : R ≤ Real.sqrt n := by dsimp only [R]; rw [Real.exp_half]; exact Real.sqrt_le_sqrt hlo.le
    have hval : |m*continuousIntegerAtom Φ n t| ≤ B := by
      rw [continuousIntegerAtom,abs_mul,abs_mul,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
      calc
        _ ≤ |m| *(R⁻¹*((K:ℝ)*(H/X))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul ((inv_le_inv₀ (Real.sqrt_pos.2 hn0) hR).2 hroot) hφ (abs_nonneg _) (inv_nonneg.mpr hR.le)) (abs_nonneg _)
        _ = B := by dsimp only [B]; field_simp [hX.ne',hR.ne']
    refine max_le ?_ (mul_nonneg hB (abs_nonneg _))
    apply (neg_le_abs _).trans
    rw [show m*((ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t) =
      (m*continuousIntegerAtom Φ n t)*(ArithmeticFunction.vonMangoldt n-1) by ring,abs_mul]
    exact mul_le_mul_of_nonneg_right hval (abs_nonneg _)
  have hR2 : R^2=X := by dsimp only [R,X]; rw [sq,← Real.exp_add]; congr 1; ring
  change ∑ n ∈ J, _ ≤ _
  calc _ ≤ ∑ n ∈ J, B*|ArithmeticFunction.vonMangoldt n-1| := Finset.sum_le_sum hpt
    _ = B*∑ n ∈ J, |ArithmeticFunction.vonMangoldt n-1| := (Finset.mul_sum ..).symm
    _ ≤ B*((C+2)*H) := mul_le_mul_of_nonneg_left hcost hB
    _ = D*(Real.sqrt t)^2/R := by
      dsimp only [B,D,H,criticalWallWidth]
      rw [← hR2,show Real.exp (t/2) = R from rfl]
      field_simp [hR.ne']
    _ = D*t*Real.exp (-t/2) := by
      rw [Real.sq_sqrt (by linarith only [ht]),show -t/2 = -(t/2) by ring,Real.exp_neg]
      rfl
    _ ≤ (D*(4*Real.exp (t/4)))*Real.exp (-t/2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (t/4)]) hD) (Real.exp_pos _).le
    _ = _ := by
      rw [show D*(4*Real.exp (t/4))*Real.exp (-t/2) = (4*D)*(Real.exp (t/4)*Real.exp (-t/2)) by ring,
        ← Real.exp_add,show t/4 + -t/2 = -t/4 by ring]

/-- The endpoint error after freezing the wall price, plus the absolute
value of the signed Abel variation from the far edge of the first window. -/
def adjacentAbelDeviation (Φ : ℝ → ℝ) (γ t : ℝ) (L : ℕ) : ℝ :=
  let H := criticalWallWidth t
  let b := ⌊Real.exp t+H⌋₊
  let w := fun j : ℕ => (∫ y, Φ y)*continuousIntegerAtom Φ j t
  |(w L-γ/H)*centeredAbelPrefix b L|+
    |∑ j ∈ Finset.Ico b L, centeredAbelPrefix b j*(w j-w (j+1))|

/-- On every fixed band just beyond the first window, the signed Abel
variation and the deviation of its endpoint from the flat wall price
vanish uniformly in the upper endpoint. -/
theorem criticalState_adjacent_abel_variation {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    let m := ∫ y, Φ y
    let γ := Real.sqrt 2*(|m| *Real.sqrt (8*criticalAliasCoefficient W₀*
      ∫ y : ℝ, F y^2*Real.exp (-(8*y))))
    ∀ᶠ t : ℝ in atTop,
      let H := criticalWallWidth t
      let b := ⌊Real.exp t+H⌋₊
      ∀ L : ℕ, b < L → (L:ℝ) ≤ Real.exp t+B*H → adjacentAbelDeviation Φ γ t L < ε := by
  let m := ∫ y, Φ y
  let V := |m| *Real.sqrt (8*criticalAliasCoefficient W₀*∫ y : ℝ, F y^2*Real.exp (-(8*y)))
  let γ := Real.sqrt 2*V
  obtain ⟨_,hlaw⟩ := criticalState_oriented_wall_limit hW ht hF hc he
  obtain ⟨C,hC,hM⟩ := mangoldt_mass_on_power_width
  let D := (C+2)*B
  have hB0 := zero_lt_one.trans_le hB
  have hD : 0 < D := mul_pos (by linarith only [hC]) hB0
  let δ := ε/(4*D)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hband := eventually_critical_band_wall_atom hlaw zero_lt_one hB0 hδ
  simp only [one_mul] at hband
  have hexp : Tendsto (fun t : ℝ => Real.exp (t/4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<4))
  filter_upwards [hband,criticalWallWidth_range (η := 1) zero_lt_one le_rfl,
    eventually_ge_atTop (1:ℝ),hexp.eventually_ge_atTop B] with t hw hr ht1 hBexp
  let H := criticalWallWidth t
  let b := ⌊Real.exp t+H⌋₊
  let w := fun j : ℕ => m*continuousIntegerAtom Φ j t
  have hH : 0 < H := hr.1
  have hHB := le_mul_of_one_le_left hH.le hB
  have hlowH : Real.exp (t/4) ≤ H := by simpa only [one_mul] using hr.2.1
  have hup : B*H ≤ Real.exp t := calc
    _ ≤ Real.exp (t/4)*Real.exp (3*t/4) := mul_le_mul hBexp hr.2.2.2.1 hH.le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
  intro L hbL hL
  let I := Finset.Ioc b L
  let a := fun j : ℕ => ArithmeticFunction.vonMangoldt j-1
  have hsub : I ⊆ wallIntegerWindow t (B*H) := by
    intro j hj
    obtain ⟨hj1,hj2⟩ := Finset.mem_Ioc.mp hj
    exact Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.floor_mono (le_add_of_nonneg_right hH.le)) hj1,
      Nat.le_floor (by exact (show (j:ℝ) ≤ L by exact_mod_cast hj2).trans hL)⟩
  have hmass : ∑ j ∈ I, |a j| ≤ D*H := calc
    _ ≤ ∑ j ∈ wallIntegerWindow t (B*H), |a j| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _
    _ ≤ (C+2)*(B*H) := width_mangoldt_abs hM ht1 (hlowH.trans hHB) hup
    _ = _ := by dsimp only [D]; ring
  have hweight (j : ℕ) (hj : j ∈ I) : |w j-γ/H| ≤ δ/H := by
    obtain ⟨hj1,hj2⟩ := Finset.mem_Ioc.mp hj
    have hinc : (b:ℝ)+1 ≤ j := by exact_mod_cast hj1
    have hlow := (Nat.lt_floor_add_one (Real.exp t+H)).trans_le hinc
    have hhigh := (show (j:ℝ) ≤ L by exact_mod_cast hj2).trans hL
    have h := (hw j hlow hhigh).le
    apply (le_div_iff₀ hH).2
    calc |w j-γ/H| *H = |(w j-γ/H)*H| := by rw [abs_mul,abs_of_pos hH]
         _ = |H*w j-γ| := by congr 1; field_simp [hH.ne']; ring
         _ ≤ δ := h
  have hQ : |centeredAbelPrefix b L| ≤ D*H := (Finset.abs_sum_le_sum_abs a I).trans hmass
  have hprice : δ/H*(D*H) = ε/4 := by dsimp only [δ]; field_simp [hH.ne',hD.ne']
  have hend : |(w L-γ/H)*centeredAbelPrefix b L| ≤ ε/4 := by
    rw [abs_mul]
    exact (mul_le_mul (hweight L (Finset.mem_Ioc.mpr ⟨hbL,le_rfl⟩)) hQ (abs_nonneg _)
      (div_nonneg hδ.le hH.le)).trans_eq hprice
  have htotal : |∑ j ∈ I, a j*(w j-γ/H)| ≤ ε/4 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ j ∈ I, δ/H*|a j| := Finset.sum_le_sum fun j hj => by
             rw [abs_mul,mul_comm (δ/H)]
             exact mul_le_mul_of_nonneg_left (hweight j hj) (abs_nonneg _)
         _ ≤ _ := by rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left hmass
           (div_nonneg hδ.le hH.le)).trans_eq hprice
  have hid := centeredAbelPrefix_by_parts (fun j => w j-γ/H) (b := b) le_rfl hbL.le
  simp only [centeredAbelPrefix,Finset.Ioc_self,Finset.sum_empty,mul_zero,sub_zero,
    sub_sub_sub_cancel_right] at hid
  have hab : |∑ j ∈ Finset.Ico b L, centeredAbelPrefix b j*(w j-w (j+1))| ≤ ε/4+ε/4 := by
    have hv : (∑ j ∈ Finset.Ico b L, centeredAbelPrefix b j*(w j-w (j+1))) =
        (∑ j ∈ I, a j*(w j-γ/H))-(w L-γ/H)*centeredAbelPrefix b L := eq_sub_of_add_eq' hid.symm
    rw [hv]
    exact (abs_sub ..).trans (add_le_add htotal hend)
  exact (add_le_add hend hab).trans_lt (by linarith only [hε])

/-- The oriented signed contribution at the critical width, in the original
integer normalization. -/
def criticalWidthSignedReading (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ wallIntegerWindow t (criticalWallWidth t),
    (∫ u, Φ u)*((ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t)

/-- The signed window retains the local Chebyshev excess. The inner fraction
is paid by a uniform short-interval sieve before the fraction tends to zero. -/
theorem tendsto_criticalWidthSignedReading_sub_chebyshev {Φ : ℝ → ℝ} {m L : ℝ}
    (hm : m = ∫ u, Φ u)
    (hlaw : Tendsto (fun k : ℝ => (m*Φ (-k))*Real.sqrt (Real.log (1/k))) (𝓝[>] 0) (𝓝 L)) :
    let γ := Real.sqrt 2*L
    Tendsto (fun t : ℝ => criticalWidthSignedReading Φ t -
      γ*((Chebyshev.psi (Real.exp t+criticalWallWidth t)-Chebyshev.psi (Real.exp t))/criticalWallWidth t-1))
      atTop (𝓝 0) := by
  let γ := Real.sqrt 2*L
  let H := criticalWallWidth
  let J := fun t : ℝ => wallIntegerWindow t (H t)
  let a := fun n : ℕ => ArithmeticFunction.vonMangoldt n-1
  let w := fun (t : ℝ) (n : ℕ) => H t*(m*continuousIntegerAtom Φ n t)
  obtain ⟨C,hC,hM⟩ := mangoldt_mass_on_power_width
  obtain ⟨B,hB,hcap⟩ := critical_width_atom_cap hlaw
  let D := C+2
  let M := B+|γ|+1
  have hD : 0 < D := by dsimp only [D]; linarith only [hC]
  have hMpos : 0 < M := by dsimp only [M]; positivity
  have herr : Tendsto (fun t => (∑ n ∈ J t, a n*(w t n-γ))/H t) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let η := min 1 (ε/(4*(M*D)))
    let e := ε/(4*D)
    have hη : 0 < η := lt_min zero_lt_one (div_pos hε (by positivity))
    have hη' : η ≤ 1 := min_le_left ..
    have he : 0 < e := div_pos hε (by positivity)
    have hout := eventually_critical_band_wall_atom hlaw hη zero_lt_one he
    simp only [one_mul] at hout
    filter_upwards [hcap, criticalWallWidth_range hη hη',eventually_ge_atTop (1:ℝ),hout] with t htcap hrange ht hout
    let I := wallIntegerWindow t (η*H t)
    have hHpos : 0 < H t := hrange.1
    have hIH : η*H t ≤ H t := hrange.2.2.1
    have hHX : H t ≤ Real.exp t := hrange.2.2.2.1.trans hrange.2.2.2.2
    have hsub : I ⊆ J t := by
      intro n hn
      obtain ⟨hu,hv⟩ := Finset.mem_Ioc.mp hn
      exact Finset.mem_Ioc.mpr ⟨hu,hv.trans (Nat.floor_mono (by linarith only [hIH]))⟩
    have hsi (n : ℕ) (hn : n ∈ I) : |w t n-γ| ≤ M := by
      apply (abs_sub _ _).trans
      have hb := htcap n (hsub hn)
      change |w t n| ≤ B at hb
      dsimp only [M]; linarith only [hb]
    have hso (n : ℕ) (hn : n ∈ J t) (hni : n ∉ I) : |w t n-γ| ≤ e := by
      obtain ⟨hnl,hnu⟩ := Finset.mem_Ioc.mp hn
      have hlo : ⌊Real.exp t+η*H t⌋₊ < n := lt_of_not_ge fun h => hni (Finset.mem_Ioc.mpr ⟨hnl,h⟩)
      have hlow := (Nat.floor_lt (add_nonneg (Real.exp_pos t).le (mul_nonneg hη.le hHpos.le))).mp hlo
      have hu := (Nat.le_floor_iff (add_nonneg (Real.exp_pos t).le hHpos.le)).mp hnu
      exact (hout n hlow hu).le
    have hp := sum_wall_weight_error (a := a) hsub he.le hsi hso
    have hsmall := width_mangoldt_abs hM ht hrange.2.1 (hIH.trans hHX)
    have hfull := width_mangoldt_abs hM ht (hrange.2.1.trans hIH) hHX
    change ∑ n ∈ I, |a n| ≤ D*(η*H t) at hsmall
    change ∑ n ∈ J t, |a n| ≤ D*H t at hfull
    have hcη : (M*D)*η ≤ ε/4 := by
      have hηbound : η ≤ ε/(4*(M*D)) := min_le_right _ _
      apply (mul_le_mul_of_nonneg_left hηbound (mul_nonneg hMpos.le hD.le)).trans_eq
      field_simp [hMpos.ne',hD.ne']
    have hce : e*D=ε/4 := by dsimp only [e]; field_simp [hD.ne']
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hHpos,div_lt_iff₀ hHpos]
    apply hp.trans_lt
    calc _ ≤ M*(D*(η*H t))+e*(D*H t) := add_le_add (mul_le_mul_of_nonneg_left hsmall hMpos.le)
             (mul_le_mul_of_nonneg_left hfull he.le)
      _ = ((M*D)*η+e*D)*H t := by ring
      _ < _ := mul_lt_mul_of_pos_right (by rw [hce]; linarith only [hcη,hε]) hHpos
  have hHinf : Tendsto H atTop atTop := by
    have he := Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<1/4))
    apply tendsto_atTop_mono' _ _ he
    filter_upwards [criticalWallWidth_range (η := 1) zero_lt_one le_rfl] with t ht
    simpa only [id_eq,Function.comp_apply,one_mul,show (1/4:ℝ)*t=t/4 by ring] using ht.2.1
  have hcard : Tendsto (fun t => ((J t).card:ℝ)/H t-1) atTop (𝓝 0) := by
    refine (tendsto_zero_iff_abs_tendsto_zero _).mpr (squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
      ((tendsto_const_nhds (x := (1:ℝ))).div_atTop hHinf))
    filter_upwards [hHinf.eventually_gt_atTop 0] with t ht
    have hx := Real.exp_pos t
    have hxy := le_add_of_nonneg_right (a := Real.exp t) ht.le
    have h1 := Nat.floor_le hx.le
    have h2 := Nat.floor_le (hx.le.trans hxy)
    have h3 := Nat.lt_floor_add_one (Real.exp t)
    have h4 := Nat.lt_floor_add_one (Real.exp t+H t)
    dsimp only [Function.comp_apply,J,wallIntegerWindow]
    rw [Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono hxy)]
    rw [div_sub_one ht.ne',abs_div,abs_of_pos ht]
    apply div_le_div_of_nonneg_right _ ht.le
    rw [abs_le]; constructor <;> linarith only [h1,h2,h3,h4]
  have hrest := herr.sub (hcard.const_mul γ)
  rw [mul_zero,sub_zero] at hrest
  apply hrest.congr'
  filter_upwards [hHinf.eventually_gt_atTop 0] with t ht
  have hx := Real.exp_pos t
  have hs : Chebyshev.psi (Real.exp t+H t)-Chebyshev.psi (Real.exp t)=
      ∑ n ∈ J t, ArithmeticFunction.vonMangoldt n := by
    dsimp only [J,wallIntegerWindow,Chebyshev.psi]
    rw [← Finset.sum_Ioc_consecutive (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))
      (Nat.zero_le ⌊Real.exp t⌋₊) (Nat.floor_mono (le_add_of_nonneg_right ht.le))]
    ring
  have hsplit : (∑ n ∈ J t, a n*(w t n-γ)) =
      H t*criticalWidthSignedReading Φ t-γ*((∑ n ∈ J t, ArithmeticFunction.vonMangoldt n)-(J t).card) := by
    have hcount : (∑ n ∈ J t, a n) = (∑ n ∈ J t, ArithmeticFunction.vonMangoldt n)-(J t).card := by
      simp only [a,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
    have hread : criticalWidthSignedReading Φ t =
        ∑ n ∈ J t, m*(a n*continuousIntegerAtom Φ n t) := by rw [hm]; rfl
    rw [← hcount,hread,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl fun n _ => ?_
    dsimp only [w]; ring
  change _ = criticalWidthSignedReading Φ t -
    γ*((Chebyshev.psi (Real.exp t+H t)-Chebyshev.psi (Real.exp t))/H t-1)
  rw [hs,hsplit]; field_simp [ht.ne']; ring

/-- Telescoping along successive interval endpoints detects any slope below
the asymptotic mean, even if the width depends on the left endpoint. -/
private theorem frequently_increment_above_mean {f h : ℝ → ℝ}
    (hf : Tendsto (fun x => f x/x) atTop (𝓝 1)) (hh : ∀ᶠ x in atTop, 1 ≤ h x)
    {c : ℝ} (hc : c < 1) : ∃ᶠ x in atTop, c*h x ≤ f (x+h x)-f x := by
  rw [frequently_atTop]
  intro Z
  by_contra hfail
  push Not at hfail
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hh
  let U := max 1 (max Y Z)
  have hUY : Y ≤ U := (le_max_left Y Z).trans (le_max_right ..)
  have hUZ : Z ≤ U := (le_max_right Y Z).trans (le_max_right ..)
  let x : ℕ → ℝ := fun n => (fun v => v+h v)^[n] U
  have hx0 : x 0=U := rfl
  have hstep (n : ℕ) : x (n+1)=x n+h (x n) := Function.iterate_succ_apply' _ _ _
  have hbase (n : ℕ) : U+n ≤ x n := by
    induction n with
    | zero => simp only [Nat.cast_zero,add_zero,hx0,le_refl]
    | succ n ih =>
      have hU : U ≤ x n := by linarith only [ih,Nat.cast_nonneg (α := ℝ) n]
      rw [hstep,Nat.cast_add_one]
      linarith only [ih,hY _ (hUY.trans hU)]
  have hUX (n : ℕ) : U ≤ x n := by linarith only [hbase n,Nat.cast_nonneg (α := ℝ) n]
  have hcum (n : ℕ) : f (x n)-c*x n ≤ f U-c*U := by
    induction n with
    | zero => rw [hx0]
    | succ n ih =>
      have hbad := hfail (x n) (hUZ.trans (hUX n))
      rw [hstep]
      linarith only [ih,hbad]
  have hxt : Tendsto x atTop atTop := tendsto_atTop_mono hbase (tendsto_atTop_add_const_left atTop U tendsto_natCast_atTop_atTop)
  have hlim := (hf.sub_const c).pos_mul_atTop (sub_pos.mpr hc) tendsto_id
  have hdiv : Tendsto (fun v => f v-c*v) atTop atTop := hlim.congr' <|
    (eventually_gt_atTop (0:ℝ)).mono fun v hv => by
      change (f v/v-c)*v=f v-c*v; field_simp [hv.ne']
  obtain ⟨n,hn⟩ := ((hdiv.comp hxt).eventually_gt_atTop (f U-c*U)).exists
  exact (not_lt_of_ge (hcum n)) hn

private theorem frequently_signed_window_ge {Φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (h : Tendsto (fun t : ℝ => criticalWidthSignedReading Φ t -
      γ*((Chebyshev.psi (Real.exp t+criticalWallWidth t)-Chebyshev.psi (Real.exp t))/criticalWallWidth t-1))
      atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ t : ℝ in atTop, -ε < criticalWidthSignedReading Φ t := by
  let H := fun x : ℝ => criticalWallWidth (Real.log x)
  have hwidth (t : ℝ) (ht : 1 ≤ t) : 1 ≤ criticalWallWidth t := by
    have hsr : 1 ≤ Real.sqrt t := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by linarith only [ht])) hsr
  have hh : ∀ᶠ x : ℝ in atTop, 1 ≤ H x :=
    (Real.tendsto_log_atTop.eventually_ge_atTop 1).mono fun x hx => hwidth _ hx
  let b := ε/(2*γ)
  have hb : 0 < b := div_pos hε (by positivity)
  have hrec := frequently_increment_above_mean _root_.RHTower.FreeLagTrace.tendsto_psi_div hh
    (by linarith only [hb] : 1-b < 1)
  obtain ⟨V,hV⟩ := eventually_atTop.mp (h.eventually_const_lt (by linarith only [hε] : -ε/2 < 0))
  rw [frequently_atTop]
  intro T
  let U := max T (max V 1)
  obtain ⟨x,hx,hq⟩ := frequently_atTop.mp hrec (Real.exp U)
  have hx0 := (Real.exp_pos U).trans_le hx
  have hU : U ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have htV := ((le_max_left V 1).trans (le_max_right ..)).trans hU
  have ht1 := ((le_max_right V 1).trans (le_max_right ..)).trans hU
  have hH : 0 < H x := zero_lt_one.trans_le (hwidth _ ht1)
  refine ⟨Real.log x,(le_max_left ..).trans hU,?_⟩
  have hq' : 1-b ≤ (Chebyshev.psi (x+H x)-Chebyshev.psi x)/H x := (le_div_iff₀ hH).2 hq
  have hlo := hV (Real.log x) htV
  rw [Real.exp_log hx0] at hlo
  have hζ := mul_le_mul_of_nonneg_left (sub_le_sub_right hq' 1) hγ.le
  have hεb : γ*b=ε/2 := by dsimp only [b]; field_simp [hγ.ne']
  change -ε/2 < criticalWidthSignedReading Φ (Real.log x) -
    γ*((Chebyshev.psi (x+H x)-Chebyshev.psi x)/H x-1) at hlo
  linarith only [hlo,hζ,hεb]

/-- At the first width of nonvanishing adverse mass, the oriented signed wall
sum reads the genuine short-interval Chebyshev excess. The prime number
theorem supplies arbitrarily late readings above every fixed negative level. -/
theorem riemannHypothesis_or_signed_critical_width_chebyshev_excess : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (γ : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 < γ ∧
      γ = Real.sqrt 2 * (|∫ u, Φ u| * Real.sqrt (8*criticalAliasCoefficient W₀*
        ∫ u : ℝ, F u^2*Real.exp (-(8*u)))) ∧
      Tendsto (fun t : ℝ => criticalWidthSignedReading Φ t -
        γ*((Chebyshev.psi (Real.exp t+criticalWallWidth t)-Chebyshev.psi (Real.exp t))/criticalWallWidth t-1))
        atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ᶠ t : ℝ in atTop, -ε < criticalWidthSignedReading Φ t := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,_,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨hL,hlaw⟩ := criticalState_oriented_wall_limit hW ht hF hc he
  have hread := tendsto_criticalWidthSignedReading_sub_chebyshev rfl hlaw
  have hγ := mul_pos (by positivity : 0 < Real.sqrt 2) hL
  exact Or.inr ⟨W₀,F,Φ,_,hW,ht,hF,hc,he,hγ,rfl,hread,
    fun _ hε => frequently_signed_window_ge hγ hread hε⟩

/-- One forced state has vanishing signed variation on every fixed adjacent
critical band and an exponentially small remote rising cost on every late mask. -/
theorem riemannHypothesis_or_adjacent_and_remote_abel : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (γ D : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 < γ ∧ 0 ≤ D ∧
      (∀ (B ε : ℝ), 1 ≤ B → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ L : ℕ, ⌊Real.exp t+criticalWallWidth t⌋₊ < L →
          (L:ℝ) ≤ Real.exp t+B*criticalWallWidth t → adjacentAbelDeviation Φ γ t L < ε) ∧
      ∀ (T : ℝ) (A : Set ℝ), MeasurableSet A →
        let f := fun t => remoteRisingAbelLoss Φ t*fractionalPrimeTest (T-t)
        IntegrableOn f (A ∩ Ioi (T/6)) ∧ (∫ t in A ∩ Ioi (T/6), f t) ≤ D*Real.exp (-T/6) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,_,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨hL,_⟩ := criticalState_oriented_wall_limit hW ht hF hc he
  obtain ⟨D,hD,hremote⟩ := criticalState_remote_rising_test hW ht hF hc he
  exact Or.inr ⟨W₀,F,Φ,_,D,hW,ht,hF,hc,he,mul_pos (by positivity : 0 < Real.sqrt 2) hL,
    hD,fun _ _ hB hε => criticalState_adjacent_abel_variation hW ht hF hc he hB hε,hremote⟩

#print axioms riemannHypothesis_or_adjacent_and_remote_abel
#print axioms lipschitz_adverse_critical_width_tendsto_zero
#print axioms riemannHypothesis_or_signed_critical_width_chebyshev_excess
end GaloisForLFunctions.ExclusionOfTheCriticalState
