import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PrimeSupportAcrossLateCriticalWidthWindows
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TwoSidedPrimePrefixesAtAlmostEveryCenter
import GaloisForLFunctions.RHTower.FermiNymanLogMobiusHead

/-!
# A common lower bound for all future centered Mangoldt increments

The increasing lower envelope of a Chebyshev count with positive drift has
the same mean slope. Where the envelope rises across a fourth-root interval,
the count at the starting point is already near its minimum on the full
future ray. The sieve bounds the height of each rise, hence such starting
points occupy positive relative measure in every late fixed-ratio interval.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private def futureChebyshevFloor (c x : ℝ) := sInf ((fun y : ℝ => Chebyshev.psi y-c*y) '' Ici x)

/-- The right-hand minimum of the Chebyshev count with a positive linear
drift has exactly the same first-order growth as the count itself. -/
private theorem futureChebyshevFloor_rate {c : ℝ} (hc : c < 1) :
    Tendsto (fun x => futureChebyshevFloor c x/x) atTop (𝓝 (1-c)) := by
  let g := fun x : ℝ => Chebyshev.psi x-c*x
  have hr : Tendsto (fun x => g x/x) atTop (𝓝 (1-c)) := by
    apply (_root_.RHTower.FreeLagTrace.tendsto_psi_div.sub_const c).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    dsimp only [g]; field_simp [hx.ne'] <;> ring
  have hs := sub_pos.mpr hc
  have hbound : ∀ᶠ x : ℝ in atTop, BddBelow (g '' Ici x) := by
    obtain ⟨U,hU⟩ := eventually_atTop.mp (hr.eventually_const_lt hs)
    filter_upwards [eventually_ge_atTop U,eventually_gt_atTop (0:ℝ)] with x hxU hx
    refine ⟨0,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    have hy0 := hx.trans_le hy
    have h := (lt_div_iff₀ hy0).1 (hU y (hxU.trans hy))
    simpa only [zero_mul] using h.le
  refine tendsto_order.2 ⟨fun a ha => ?_,fun a ha => ?_⟩
  · obtain ⟨r,hr0,hrs⟩ := exists_between (max_lt ha hs)
    have har := (le_max_left a 0).trans_lt hr0
    have hpos := (le_max_right a 0).trans_lt hr0
    obtain ⟨U,hU⟩ := eventually_atTop.mp (hr.eventually_const_lt hrs)
    filter_upwards [eventually_ge_atTop U,eventually_gt_atTop (0:ℝ)] with x hxU hx
    apply har.trans_le ((le_div_iff₀ hx).2 ?_)
    refine le_csInf (s := g '' Ici x) ⟨g x,x,Set.left_mem_Ici,rfl⟩ ?_
    rintro _ ⟨y,hy,rfl⟩
    exact (mul_le_mul_of_nonneg_left hy hpos.le).trans
      ((lt_div_iff₀ (hx.trans_le hy)).1 (hU y (hxU.trans hy))).le
  · filter_upwards [hbound,eventually_gt_atTop (0:ℝ),hr.eventually_lt_const ha] with x hxB hx hxg
    have h := csInf_le hxB (show g x ∈ g '' Ici x from ⟨x,Set.left_mem_Ici,rfl⟩)
    exact (div_le_div_of_nonneg_right h hx.le).trans_lt hxg


private theorem chebyshev_drift_boundedBelow {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    BddBelow (range fun y : ℝ => Chebyshev.psi y-c*y) := by
  obtain ⟨U,hU⟩ := eventually_atTop.mp (_root_.RHTower.FreeLagTrace.tendsto_psi_div.eventually_const_lt hc1)
  let Y := max U 1
  have hY : 0 ≤ Y := zero_le_one.trans (le_max_right ..)
  refine ⟨-(c*Y),?_⟩
  rintro _ ⟨y,rfl⟩
  by_cases h : Y ≤ y
  · have hy := (zero_lt_one.trans_le (le_max_right U 1)).trans_le h
    have hq := (lt_div_iff₀ hy).1 (hU y ((le_max_left U 1).trans h))
    linarith only [hq,mul_nonneg hc0 hY]
  · have hp := mul_le_mul_of_nonneg_left (le_of_not_ge h) hc0
    linarith only [hp,Chebyshev.psi_nonneg y]

private theorem futureChebyshevFloor_mono {c : ℝ} (hB : BddBelow (range fun y : ℝ => Chebyshev.psi y-c*y)) :
    Monotone (futureChebyshevFloor c) := by
  intro x y hxy
  refine le_csInf (s := (fun y : ℝ => Chebyshev.psi y-c*y) '' Ici y) ⟨_,y,Set.left_mem_Ici,rfl⟩ ?_
  rintro _ ⟨z,hz,rfl⟩
  exact csInf_le (hB.mono (image_subset_range ..)) ⟨z,hxy.trans hz,rfl⟩

/-- A strict rise of the future minimum certifies *every* later prime
increment. Its height is bounded by the actual primes in the short cell. -/
private theorem futureChebyshevFloor_increment {c x H : ℝ} (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hB : BddBelow (range fun y : ℝ => Chebyshev.psi y-c*y)) :
    futureChebyshevFloor c (x+H)-futureChebyshevFloor c x ≤ Chebyshev.psi (x+H)-Chebyshev.psi x ∧
    (futureChebyshevFloor c x < futureChebyshevFloor c (x+H) →
      ∀ y ≥ x, c*(y-x)-c*H ≤ Chebyshev.psi y-Chebyshev.psi x) := by
  let g := fun y => Chebyshev.psi y-c*y
  let M := futureChebyshevFloor c
  have hle (a y : ℝ) (h : a ≤ y) : M a ≤ g y :=
    csInf_le (hB.mono (image_subset_range ..)) ⟨y,h,rfl⟩
  have hlow (r : ℝ) (h : ∀ y ≥ x, r ≤ g y) : r ≤ M x := by
    refine le_csInf (s := g '' Ici x) ⟨g x,x,Set.left_mem_Ici,rfl⟩ ?_
    rintro _ ⟨y,hy,rfl⟩; exact h y hy
  have hpx := Chebyshev.psi_mono (le_add_of_nonneg_right (a := x) hH)
  constructor
  · apply sub_le_comm.mp
    apply hlow
    intro y hy
    by_cases hxy : x+H ≤ y
    · linarith only [hle (x+H) y hxy,hpx]
    · have hp := Chebyshev.psi_mono hy
      have hcy := mul_le_mul_of_nonneg_left (le_of_not_ge hxy) hc
      have hb := hle (x+H) (x+H) le_rfl
      dsimp only [g] at hb ⊢; linarith only [hb,hcy,hp]
  · intro hraise y hy
    have hfloor : min (g x-c*H) (M (x+H)) ≤ M x := by
      apply hlow
      intro z hz
      by_cases h : x+H ≤ z
      · exact (min_le_right ..).trans (hle _ _ h)
      · apply (min_le_left ..).trans
        have hp := Chebyshev.psi_mono hz
        have hd := mul_le_mul_of_nonneg_left (le_of_not_ge h) hc
        dsimp only [g]; linarith only [hp,hd]
    have hr : g x-c*H ≤ M x := (min_le_iff.mp hfloor).resolve_right hraise.not_ge
    have hg := hr.trans (hle _ y hy)
    dsimp only [g] at hg; linarith only [hg]

private def futurePrimeCellWidth (R x : ℝ) := Real.exp (Real.log (R*x)/4)

private theorem futurePrimeCellWidth_sublinear {R : ℝ} (hR : 0 < R) :
    Tendsto (fun x => futurePrimeCellWidth R x/x) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.const_mul_atTop_of_neg (by norm_num : (-3/4:ℝ)<0)
  have h := (Real.tendsto_exp_atBot.comp hlog).const_mul (Real.exp (Real.log R/4))
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  dsimp only [futurePrimeCellWidth,Function.comp_apply]
  rw [Real.log_mul hR.ne' hx.ne',add_div,Real.exp_add]
  have he : Real.exp ((-3/4)*Real.log x) * x = Real.exp (Real.log x/4) := by
    calc _ = Real.exp ((-3/4)*Real.log x)*Real.exp (Real.log x) := congrArg (_*·) (Real.exp_log hx).symm
         _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (eq_div_iff hx.ne').mpr
  rw [mul_assoc,he]

private theorem futurePrimeCellWidth_sieve {R : ℝ} (hR : 1 < R) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Ioc x (R*x),
      Chebyshev.psi (u+futurePrimeCellWidth R x)-Chebyshev.psi u ≤ C*futurePrimeCellWidth R x := by
  obtain ⟨C,hC,hM⟩ := mangoldt_mass_on_power_width
  have hR0 := zero_lt_one.trans hR
  have hH := futurePrimeCellWidth_sublinear hR0
  refine ⟨C+1,by linarith only [hC],?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1),hH.eventually_lt_const zero_lt_one] with x hx hh
  intro u hu
  let H := futurePrimeCellWidth R x
  have hx0 := (Real.exp_pos _).trans_le hx
  have hu0 := hx0.trans hu.1
  have hHt : 1 ≤ Real.log u := (Real.le_log_iff_exp_le hu0).mpr (hx.trans hu.1.le)
  have hHr : Real.exp (Real.log u/4) ≤ H := Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (Real.log_le_log hu0 hu.2) (by norm_num))
  have hHl := (div_lt_one hx0).mp hh
  have hHu : H ≤ Real.exp (Real.log u) := (hHl.le.trans hu.1.le).trans (Real.exp_log hu0).symm.le
  have hm := hM (Real.log u) hHt H hHr hHu
  rw [Real.exp_log hu0] at hm
  have hp : 0 < H := Real.exp_pos _
  have hd := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc (le_add_of_nonneg_right (a := u) hp.le)
  change Chebyshev.psi (u+H)-Chebyshev.psi u ≤ (C+1)*H
  rw [hd]; exact hm.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hp.le)

/-- In every fixed-ratio interval a set of starting points of positive relative
measure supports all future Mangoldt increments simultaneously. The additive
error is the fourth-root sieve width of the right endpoint. -/
theorem positive_measure_of_all_future_chebyshev_increments {c R : ℝ} (hc : 0 < c)
    (hc1 : c < 1) (hR : 1 < R) : ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ x : ℝ in atTop,
      ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Ioc x (R*x) ∧ κ*x ≤ volume.real A ∧
        ∀ u ∈ A, ∀ y ≥ u, c*(y-u)-c*Real.exp (Real.log (R*x)/4) ≤ Chebyshev.psi y-Chebyshev.psi u := by
  let r := 1-c
  let M := futureChebyshevFloor c
  let f := fun y => M y/r
  let H := futurePrimeCellWidth R
  have hr : 0 < r := sub_pos.mpr hc1
  have hB := chebyshev_drift_boundedBelow hc.le hc1
  have hM := futureChebyshevFloor_mono hB
  have hmf : Monotone f := fun _ _ h => div_le_div_of_nonneg_right (hM h) hr.le
  have hfr : Tendsto (fun y => f y/y) atTop (𝓝 1) := by
    have h := (futureChebyshevFloor_rate hc1).div_const r
    change Tendsto _ _ (𝓝 (r/r)) at h
    rw [div_self hr.ne'] at h
    exact h.congr fun y => by dsimp only [f,M]; ring
  have hpos (x : ℝ) : 0 < H x := Real.exp_pos _
  have hsub := futurePrimeCellWidth_sublinear (zero_lt_one.trans hR)
  have hmean := tendsto_frozen_window_mean hmf hfr (Eventually.of_forall hpos) hsub hR
  have hnear := hmean.eventually_const_lt (show (1/2)*(R-1) < R-1 by linarith only [hR])
  obtain ⟨C,hC,hbound⟩ := futurePrimeCellWidth_sieve hR
  let D := C/r
  have hD : 0 < D := div_pos (zero_lt_one.trans_le hC) hr
  refine ⟨(R-1)/(2*D),div_pos (sub_pos.mpr hR) (by positivity),?_⟩
  filter_upwards [hnear,hbound,eventually_gt_atTop (0:ℝ)] with x hav hmax hx
  have hh := hpos x
  have hxy : x ≤ R*x := le_mul_of_one_le_left hx.le hR.le
  let q := fun u => (f (u+H x)-f u)/H x
  have hsh := HTGeometry.monotone_comp_add_right hmf (H x)
  have hm : Measurable q := (hsh.measurable.sub hmf.measurable).div_const _
  have hi : IntervalIntegrable q volume x (R*x) := (hsh.intervalIntegrable.sub hmf.intervalIntegrable).div_const _
  have hval : (1/2)*(R*x-x) ≤ ∫ u in x..R*x, q u := by
    dsimp only [q]; rw [intervalIntegral.integral_div,le_div_iff₀ hh]
    have hav' := (lt_div_iff₀ (mul_pos hh hx)).mp hav
    calc _ = ((1/2)*(R-1))*(H x*x) := by ring
         _ ≤ _ := hav'.le
  have hcap (u : ℝ) (hu : u ∈ Ioc x (R*x)) : q u ≤ D := by
    dsimp only [q,f,D]
    rw [← sub_div,div_le_iff₀ hh,div_mul_eq_mul_div,div_le_div_iff_of_pos_right hr]
    exact (futureChebyshevFloor_increment hc.le hh.le hB).1.trans (hmax u hu)
  obtain ⟨A,hmA,hAI,hgood,hmass⟩ := exists_positive_measure_of_lower_interval_mean hxy
    (le_refl (0:ℝ)) hm hi hval hcap
  refine ⟨A,hmA,hAI,?_,fun u hu => ?_⟩
  · rw [div_mul_eq_mul_div,div_le_iff₀ (mul_pos (by norm_num) hD)]
    linarith only [hmass]
  · have hz := hgood u hu
    change 0 < (M (u+H x)/r-M u/r)/H x at hz
    have hfpos := (lt_div_iff₀ hh).mp hz
    rw [zero_mul,sub_pos,div_lt_div_iff_of_pos_right hr] at hfpos
    exact (futureChebyshevFloor_increment hc.le hh.le hB).2 hfpos

private theorem centered_future_increment_of_chebyshev {u y c H : ℝ} (hu0 : 0 ≤ u) (hy : u ≤ y)
    (hψ : c*(y-u)-c*H ≤ Chebyshev.psi y-Chebyshev.psi u) :
    -(1-c)*(y-u)-c*H-1 ≤ ∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1) := by
  have hd := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc hy
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc,
    Nat.cast_sub (Nat.floor_mono hy),← hd]
  linarith only [hψ,Nat.floor_le (hu0.trans hy),Nat.lt_floor_add_one u]

/-- The literal integer reference contributes at most one endpoint unit to the
same lower bound, simultaneously over the entire future ray. -/
theorem positive_measure_of_all_future_centered_mangoldt_increments {c R : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hR : 1 < R) : ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ x : ℝ in atTop,
      ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Ioc x (R*x) ∧ κ*x ≤ volume.real A ∧
      ∀ u ∈ A, ∀ y ≥ u, -(1-c)*(y-u)-c*Real.exp (Real.log (R*x)/4)-1 ≤
        ∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1) := by
  obtain ⟨κ,hκ,hA⟩ := positive_measure_of_all_future_chebyshev_increments hc hc1 hR
  refine ⟨κ,hκ,?_⟩
  filter_upwards [hA,eventually_gt_atTop (0:ℝ)] with x ha hx
  obtain ⟨A,hm,hAI,hmass,hall⟩ := ha
  refine ⟨A,hm,hAI,hmass,fun u hu y hy => ?_⟩
  have hu0 := hx.trans (hAI hu).1
  exact centered_future_increment_of_chebyshev hu0.le hy (hall u hu y hy)

#print axioms positive_measure_of_all_future_centered_mangoldt_increments

/-- Ordered large-divisor contribution to the literal centered Mangoldt count.
For the small divisors only the linear part of the multiples count is used.
The integer reference is kept at both original endpoints. -/
def lateDivisorCenteredCount (D : ℕ) (u y : ℝ) : ℝ :=
  let w := fun d : ℕ => -((ArithmeticFunction.moebius d : ℤ):ℝ)*Real.log d
  let N := fun d : ℕ => (⌊y/(d:ℝ)⌋:ℝ)-(⌊u/(d:ℝ)⌋:ℝ)
  (∑ d ∈ Finset.Ioc D ⌊y⌋₊, w d*N d) +
    (∑ d ∈ Finset.Ioc 0 D, w d*((y-u)/d)) - ((⌊y⌋₊:ℝ)-(⌊u⌋₊:ℝ))

/-- The small-divisor rounding cost is uniform in the upper endpoint. -/
theorem centered_count_sub_lateDivisor_le {u y : ℝ} (hu : 0 ≤ u) (hy : u ≤ y)
    {D : ℕ} (hDu : D ≤ ⌊u⌋₊) :
    |(∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1))-lateDivisorCenteredCount D u y|
      ≤ D*Real.log D := by
  let w := fun d : ℕ => -((ArithmeticFunction.moebius d : ℤ):ℝ)*Real.log d
  let N := fun d : ℕ => (⌊y/(d:ℝ)⌋:ℝ)-(⌊u/(d:ℝ)⌋:ℝ)
  let S := Finset.Ioc 0 D
  let N₀ := ⌊y⌋₊
  have hDy := hDu.trans (Nat.floor_mono hy)
  have hsets : Finset.Icc 1 N₀=Finset.Ioc 0 N₀ := by ext d; simp only [Finset.mem_Icc,Finset.mem_Ioc]; omega
  have hrow (s : ℝ) (hs : 0 ≤ s) (hs' : ⌊s⌋₊ ≤ N₀) :
      (∑ d ∈ Finset.Ioc 0 N₀, w d*(⌊s/(d:ℝ)⌋:ℝ)) = Chebyshev.psi s := by
    have hh := _root_.RHTower.sum_moebius_log_mul_floor N₀ hs hs'
    rw [hsets] at hh
    dsimp only [w]; simp only [neg_mul,Finset.sum_neg_distrib]; linarith only [hh]
  have hfull : (∑ d ∈ S, w d*N d)+(∑ d ∈ Finset.Ioc D N₀, w d*N d)=Chebyshev.psi y-Chebyshev.psi u := by
    change (∑ d ∈ Finset.Ioc 0 D, w d*N d)+(∑ d ∈ Finset.Ioc D N₀, w d*N d)=_
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le D) hDy]
    simp only [N,mul_sub,Finset.sum_sub_distrib]
    rw [hrow y (hu.trans hy) le_rfl,hrow u hu (Nat.floor_mono hy)]
  have hψ := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc hy
  have hdiff : (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1))-lateDivisorCenteredCount D u y =
      ∑ d ∈ S, w d*(N d-(y-u)/d) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono hy),← hψ,← hfull]
    change _ - ((∑ d ∈ Finset.Ioc D N₀, w d*N d)+(∑ d ∈ S, w d*((y-u)/d))-((N₀:ℝ)-(⌊u⌋₊:ℝ))) = _
    simp only [mul_sub,Finset.sum_sub_distrib]; ring
  rw [hdiff]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _d ∈ S, Real.log D := by
         apply Finset.sum_le_sum
         intro d hd
         have hmem := Finset.mem_Ioc.mp hd
         have hlog := Real.log_le_log (by exact_mod_cast hmem.1 : (0:ℝ)<d) (by exact_mod_cast hmem.2 : (d:ℝ) ≤ D)
         have hm : |((ArithmeticFunction.moebius d : ℤ):ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
         have hw : |w d| ≤ Real.log D := by
           rw [show w d = -((ArithmeticFunction.moebius d:ℤ):ℝ)*Real.log d from rfl,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg _)]
           exact (mul_le_of_le_one_left (Real.log_natCast_nonneg _) hm).trans hlog
         have he : |N d-(y-u)/d| ≤ 1 := by
           dsimp only [N]; rw [sub_div,abs_le]
           constructor <;> linarith only [Int.floor_le (y/(d:ℝ)),Int.lt_floor_add_one (y/(d:ℝ)),
             Int.floor_le (u/(d:ℝ)),Int.lt_floor_add_one (u/(d:ℝ))]
         rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) he).trans hw
       _ = _ := by simp only [S,Finset.sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]

private theorem futurePrimeCellWidth_div_sqrt {R : ℝ} (hR : 0 < R) :
    Tendsto (fun x => futurePrimeCellWidth R x/Real.sqrt x) atTop (𝓝 0) := by
  have h := (Real.tendsto_exp_atBot.comp (Real.tendsto_log_atTop.const_mul_atTop_of_neg
      (by norm_num : (-1/4:ℝ)<0))).const_mul (Real.exp (Real.log R/4))
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  dsimp only [futurePrimeCellWidth,Function.comp_apply]
  rw [Real.log_mul hR.ne' hx.ne',add_div,Real.exp_add,
    show Real.sqrt x=Real.exp (Real.log x/2) by rw [Real.exp_half,Real.exp_log hx],
    mul_div_assoc,← Real.exp_sub]
  congr 2; ring

/-- One measurable set carries positive fractional-test mass, a favorable
signed state reading, and a uniform lower bound for every future centered
Mangoldt prefix. -/
theorem criticalState_all_future_prefixes_at_favorable_state_centers {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ) :
    ∀ R ε : ℝ, 1 < R → 0 < ε → ∃ c κ : ℝ, 0 < c ∧ c < 1 ∧ 0 < κ ∧ ∀ᶠ x : ℝ in atTop,
        ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Ioc x (R*x) ∧ κ*x ≤ volume.real A ∧
          κ/R^2 ≤ (∫ u in A, fractionalPrimeTest (Real.log x-Real.log u)*u⁻¹) ∧
          ∀ u ∈ A, -ε < criticalWidthSignedReading Φ (Real.log u) ∧
            ∀ y ≥ u,
              let b := -(1-c)*(y-u)-c*Real.exp (Real.log (R*x)/4)-1
              let D := ⌊Real.exp (Real.log u/4)⌋₊
              b ≤ (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1)) ∧
                b-D*Real.log D ≤ lateDivisorCenteredCount D u y := by
  obtain ⟨hL,hlaw⟩ := criticalState_oriented_wall_limit hW ht hF hc he
  let γ := Real.sqrt 2*(|∫ u, Φ u| *Real.sqrt (8*criticalAliasCoefficient W₀*∫ u : ℝ, F u^2*Real.exp (-(8*u))))
  have hγ : 0 < γ := mul_pos (by positivity) hL
  have hw := tendsto_criticalWidthSignedReading_sub_chebyshev rfl hlaw
  intro R ε hR hε
  let δ := min (1/4) (ε/(8*γ))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1/4 := min_le_left ..
  have hδε : δ*(8*γ) ≤ ε := (le_div_iff₀ (by positivity : 0 < 8*γ)).1 (min_le_right (1/4:ℝ) _)
  let c := 1-δ
  have hc0 : 0 < c := by dsimp only [c]; linarith only [hδ1]
  have hc1 : c < 1 := by dsimp only [c]; linarith only [hδ]
  obtain ⟨κ,hκ,hall⟩ := positive_measure_of_all_future_chebyshev_increments hc0 hc1 hR
  have hR0 := zero_lt_one.trans hR
  have hsm := (futurePrimeCellWidth_div_sqrt hR0).eventually_lt_const hδ
  obtain ⟨V,hV⟩ := eventually_atTop.mp (hw.eventually_const_lt (by linarith only [hε] : -ε/2 < 0))
  refine ⟨c,κ,hc0,hc1,hκ,?_⟩
  filter_upwards [hall,hsm,eventually_ge_atTop (Real.exp 1),eventually_ge_atTop (Real.exp V)] with x ha hH hxe hxV
  obtain ⟨A,hm,hAI,hmass,hfuture⟩ := ha
  have hx0 := (Real.exp_pos _).trans_le hxe
  have hk := (fractionalPrimeTest_mass_of_log_window_subset hm hx0 hR0 hAI hmass).2
  have hprefix (u : ℝ) (hu : u ∈ A) (y : ℝ) (hy : u ≤ y) :=
    centered_future_increment_of_chebyshev (hx0.trans (hAI hu).1).le hy (hfuture u hu y hy)
  have hlarge (u : ℝ) (hu : u ∈ A) (y : ℝ) (hy : u ≤ y) :
      let D := ⌊Real.exp (Real.log u/4)⌋₊;
      -(1-c)*(y-u)-c*Real.exp (Real.log (R*x)/4)-1-D*Real.log D ≤ lateDivisorCenteredCount D u y := by
    have hu0 := hx0.trans (hAI hu).1
    have hlog := (Real.le_log_iff_exp_le hu0).mpr (hxe.trans (hAI hu).1.le)
    have hDu : ⌊Real.exp (Real.log u/4)⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono
      ((Real.exp_le_exp.mpr (by linarith only [hlog] : Real.log u/4 ≤ Real.log u)).trans (Real.exp_log hu0).le)
    have hcost := (le_abs_self _).trans (centered_count_sub_lateDivisor_le hu0.le hy hDu)
    dsimp only
    linarith only [hprefix u hu y hy,hcost]
  refine ⟨A,hm,hAI,hmass,hk,fun u hu => ⟨?_,fun y hy => ⟨hprefix u hu y hy,hlarge u hu y hy⟩⟩⟩
  have hxu := (hAI hu).1
  have hu0 := hx0.trans hxu
  let w := criticalWallWidth (Real.log u)
  have hlogu := (Real.le_log_iff_exp_le hu0).mpr (hxe.trans hxu.le)
  have hl : 1 ≤ Real.sqrt (Real.log u) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlogu
  have hxy : Real.sqrt x ≤ w := by
    dsimp only [w,criticalWallWidth]; rw [Real.exp_half,Real.exp_log hu0]
    exact (Real.sqrt_le_sqrt hxu.le).trans (le_mul_of_one_le_right (Real.sqrt_nonneg _) hl)
  have hw0 := (Real.sqrt_pos.mpr hx0).trans_le hxy
  have hsmall := ((div_lt_iff₀ (Real.sqrt_pos.mpr hx0)).mp hH).le.trans (mul_le_mul_of_nonneg_left hxy hδ.le)
  have hscale : c*futurePrimeCellWidth R x ≤ δ*w := (mul_le_of_le_one_left
    (Real.exp_pos _).le hc1.le).trans hsmall
  have hfut := hfuture u hu (u+w) (le_add_of_nonneg_right hw0.le)
  rw [add_sub_cancel_left] at hfut
  have hq : 1-2*δ ≤ (Chebyshev.psi (u+w)-Chebyshev.psi u)/w := by
    apply (le_div_iff₀ hw0).2
    change c*w-c*futurePrimeCellWidth R x ≤ _ at hfut
    dsimp only [c] at hfut hscale; linarith only [hfut,hscale]
  have hΨ := hV (Real.log u) ((Real.le_log_iff_exp_le hu0).mpr (hxV.trans hxu.le))
  rw [Real.exp_log hu0] at hΨ
  change -ε/2 < criticalWidthSignedReading Φ (Real.log u)-γ*((Chebyshev.psi (u+w)-Chebyshev.psi u)/w-1) at hΨ
  have hγq := mul_le_mul_of_nonneg_left (sub_le_sub_right hq 1) hγ.le
  linarith only [hΨ,hγq,hδε,hε]

/-- Failure of RH forces one critical state carrying the simultaneous signed
integer and large-divisor bounds on every fixed-ratio window. -/
theorem riemannHypothesis_or_all_future_prefixes_at_favorable_state_centers : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ R ε : ℝ, 1 < R → 0 < ε → ∃ c κ : ℝ, 0 < c ∧ c < 1 ∧ 0 < κ ∧ ∀ᶠ x : ℝ in atTop,
        ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Ioc x (R*x) ∧ κ*x ≤ volume.real A ∧
          κ/R^2 ≤ (∫ u in A, fractionalPrimeTest (Real.log x-Real.log u)*u⁻¹) ∧
          ∀ u ∈ A, -ε < criticalWidthSignedReading Φ (Real.log u) ∧
            ∀ y ≥ u,
              let b := -(1-c)*(y-u)-c*Real.exp (Real.log (R*x)/4)-1
              let D := ⌊Real.exp (Real.log u/4)⌋₊
              b ≤ (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1)) ∧
                b-D*Real.log D ≤ lateDivisorCenteredCount D u y := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,_,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,criticalState_all_future_prefixes_at_favorable_state_centers hW ht hF hc he⟩

/-- Each late octave has positive mass for the original fractional test on
centers with a favorable signed state reading and two-sided arithmetic
control from both ends of the first window. -/
theorem riemannHypothesis_or_signed_centers_with_two_sided_prefixes : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ X : ℝ in atTop,
        ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Ioc X (2*X) ∧ κ*X ≤ volume.real A ∧
          κ/4 ≤ (∫ u in A, fractionalPrimeTest (Real.log X-Real.log u)*u⁻¹) ∧
          ∀ u ∈ A, -ε < criticalWidthSignedReading Φ (Real.log u) ∧
            ∀ z ∈ ({u,criticalPrimeWindowEnd u} : Set ℝ), ∀ y ≥ z,
              |∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1)| ≤
                ε*(y-z)+4*(2*X)^(1/5:ℝ)+1 := by
  rcases riemannHypothesis_or_all_future_prefixes_at_favorable_state_centers with h |
    ⟨W₀,F,Φ,hW,ht,hF,hc,he,hall⟩
  · exact Or.inl h
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun ε hε => ?_⟩
  obtain ⟨_,κ,_,_,hκ,hgood⟩ := hall 2 ε (by norm_num) hε
  have hhalf := half_pos hκ
  have hp := two_sided_prefixes_on_prescribed_centers
    (by norm_num : (1/6:ℝ) < 1/5) (by norm_num) hε hhalf
  refine ⟨κ/2,hhalf,?_⟩
  filter_upwards [hgood,hp,eventually_gt_atTop (0:ℝ)] with X hset hprefix hX
  obtain ⟨A,hA,hAI,hmass,_,ha⟩ := hset
  obtain ⟨G,hG,hGA,hvol,hboth⟩ := hprefix A hA (hAI.trans Ioc_subset_Icc_self)
  have hGI := hGA.trans hAI
  have hmassG : κ/2*X ≤ volume.real G := by linarith only [hmass,hvol]
  have hk := (fractionalPrimeTest_mass_of_log_window_subset hG hX (by norm_num : (0:ℝ)<2) hGI hmassG).2
  exact ⟨G,hG,hGI,hmassG,by simpa only [show (2:ℝ)^2=4 by norm_num] using hk,
    fun u hu => ⟨(ha u (hGA hu)).1,hboth u hu⟩⟩

#print axioms riemannHypothesis_or_signed_centers_with_two_sided_prefixes
#print axioms riemannHypothesis_or_all_future_prefixes_at_favorable_state_centers

end GaloisForLFunctions.ExclusionOfTheCriticalState
