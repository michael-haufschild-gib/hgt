import GaloisForLFunctions.RestrictedFactorizationCalculus.TheAbsoluteCostOfTheFourSeventhsInterior
import GaloisForLFunctions.RestrictedFactorizationCalculus.RoughDivisorInversionAtTheHyperbola
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSharpHeightOfARemovablePrimeHead
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# The power scale of relative errors in the rough interior

A choice of signs at the prime powers realizes the absolute row mass.
Its convolution is supported on rough integers and costs at most log n
at each integer. The row mass thus has growth exponent one. Dividing
the signed four-sevenths reading by this mass shifts its growth exponent
by exactly one, including at the square-root boundary.
-/
noncomputable section
open Finset Filter ArithmeticFunction _root_.RHTower.CoprimeMobius
open scoped Topology Classical ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev cut (X : ℕ) := ⌊(X : ℝ)^(4/7:ℝ)⌋₊
private abbrev signed (X : ℕ) := primePowerInteriorAtExponent (4/7) X
private abbrev mass (X : ℕ) := absoluteRoughInterior (logSquareCutoff X) X (cut X)

private theorem as_interval (y X T : ℕ) (a : ArithmeticFunction ℝ) :
    roughInteriorReading a y X T = ∑ n ∈ Ioc (min X T) X, roughFloorCoefficient y a n := by
  have split := rough_head_and_interior a y X T
  rw [rough_action_as_a_coefficient_prefix] at split
  let c := roughFloorCoefficient y a
  change quotientReading c X = roughInteriorReading a y X T + quotientReading c (min X T) at split
  have sets : Icc 1 X \ Icc 1 (min X T) = Ioc (min X T) X := by
    apply Finset.ext
    intro n
    constructor
    · intro hn
      obtain ⟨included,excluded⟩ := mem_sdiff.mp hn
      obtain ⟨pos,top⟩ := mem_Icc.mp included
      exact mem_Ioc.mpr ⟨lt_of_not_ge (fun low => excluded (mem_Icc.mpr ⟨pos,low⟩)),top⟩
    · intro hn
      obtain ⟨lo,top⟩ := mem_Ioc.mp hn
      exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt lo,top⟩,
        fun h => lo.not_ge (mem_Icc.mp h).2⟩
  rw [← sets, sum_sdiff_eq_sub (Icc_subset_Icc_right (min_le_left X T))]
  exact eq_sub_of_add_eq split.symm

private def aligned (y X T : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => if 0 ≤ interiorKernel y X T q then vonMangoldt q else -vonMangoldt q, by simp⟩

private theorem aligned_eq (y X T : ℕ) :
    absoluteRoughInterior y X T =
      roughInteriorReading (roughRestriction y (aligned y X T)) y X T := by
  rw [rough_interior_as_kernel, absoluteRoughInterior]
  apply sum_congr rfl
  intro q _
  rw [roughMangoldtWeight, roughRestriction_apply, roughRestriction_apply]
  by_cases free : IsFree (RoughReading.banned y) q
  · simp only [if_pos free, abs_mul, abs_of_nonneg (vonMangoldt_nonneg (n:=q))]
    change _ = (if 0 ≤ interiorKernel y X T q then vonMangoldt q else -vonMangoldt q) * _
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  · simp only [if_neg free, zero_mul, abs_zero]

/-- Only rough integers in the retained interval pay for the absolute
mass of all surviving prime powers. This applies even to an empty interval. -/
theorem absolute_mass_le_rough_interval_log (y X T : ℕ) :
    absoluteRoughInterior y X T ≤
      ∑ n ∈ (Ioc (min X T) X).filter (IsFree (RoughReading.banned y)), Real.log n := by
  let a := roughRestriction y (aligned y X T)
  have dom (n : ℕ) : |a n| ≤ vonMangoldt n := by
    rw [show a = roughRestriction y (aligned y X T) from rfl, roughRestriction_apply]
    split
    · change |if _ then vonMangoldt n else -vonMangoldt n| ≤ _
      split <;> simp only [abs_neg, abs_of_nonneg (vonMangoldt_nonneg (n:=n)), le_refl]
    · simpa only [abs_zero] using (vonMangoldt_nonneg (n:=n))
  have coeff : roughFloorCoefficient y a =
      roughRestriction y ((μ : ArithmeticFunction ℝ) * aligned y X T) :=
    (GaloisForLFunctions.SelbergClass.DirichletSeries.primeRestrict_mul ..).symm
  rw [aligned_eq, as_interval, sum_filter]
  apply sum_le_sum
  intro n _
  change roughFloorCoefficient y a n ≤ _
  by_cases h : IsFree (RoughReading.banned y) n
  · rw [if_pos h,roughFloorCoefficient,mul_comm (roughMobiusWeight y),mul_apply,
      Nat.sum_divisorsAntidiagonal (fun q k => a q*roughMobiusWeight y k),←vonMangoldt_sum (n:=n)]
    apply sum_le_sum
    intro q _
    have unit : |roughMobiusWeight y (n/q)| ≤ 1 := by
      rw [roughMobiusWeight,roughRestriction_apply]
      split
      · change |((ArithmeticFunction.moebius (n/q):ℤ):ℝ)| ≤ 1
        exact_mod_cast abs_moebius_le_one (n:=n/q)
      · norm_num
    calc
      _ ≤ |a q*roughMobiusWeight y (n/q)| := le_abs_self _
      _ = |a q| * |roughMobiusWeight y (n/q)| := abs_mul ..
      _ ≤ |a q| := mul_le_of_le_one_right (abs_nonneg _) unit
      _ ≤ _ := dom q
  · rw [if_neg h, coeff, roughRestriction_apply, if_neg h]

private theorem count_bound (y X T : ℕ) :
    absoluteRoughInterior y X T ≤ ((RoughReading.freeSet y X).card : ℝ) * Real.log X := by
  let S := (Ioc (min X T) X).filter (IsFree (RoughReading.banned y))
  have sub : S ⊆ RoughReading.freeSet y X := by
    intro n hn
    obtain ⟨hi, free⟩ := mem_filter.mp hn
    obtain ⟨lo, up⟩ := mem_Ioc.mp hi
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt lo, up⟩, free⟩
  apply (absolute_mass_le_rough_interval_log y X T).trans
  change (∑ n ∈ S, Real.log n) ≤ _
  calc _ ≤ ∑ n ∈ S, Real.log X := sum_le_sum fun n hn => by
           obtain ⟨lo, up⟩ := mem_Icc.mp (mem_filter.mp (sub hn)).1
           exact Real.log_le_log (Nat.cast_pos.mpr lo) (Nat.cast_le.mpr up)
       _ = (S.card : ℝ)*Real.log X := by rw [sum_const, nsmul_eq_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card sub)) (Real.log_natCast_nonneg _)

/-- Through every head the full absolute row is little-o of X log X
at any prime wall tending to infinity. -/
theorem absolute_rough_mass_saves_at_growing_walls (b : ℕ → ℕ) (grow : Tendsto b atTop atTop)
    {δ : ℝ} (hd : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ T : ℕ,
      absoluteRoughInterior (b X) X T ≤ δ * (X:ℝ) * Real.log X := by
  obtain ⟨Z,K,_,count⟩ := uniform_rough_count_at_large_walls (half_pos hd)
  filter_upwards [grow.eventually_ge_atTop Z,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (K/(δ/2))]
    with X hZ hK
  intro T
  have kc := (div_le_iff₀ (half_pos hd)).mp hK
  have c := count (b X) hZ X
  exact (count_bound _ _ _).trans (mul_le_mul_of_nonneg_right (by linarith only [c,kc]) (Real.log_natCast_nonneg _))

/-- Admissible arithmetic inputs at a fixed coordinatewise relative tolerance. -/
def insideRelativeBox (y : ℕ) (δ : ℝ) (a : ArithmeticFunction ℝ) : Prop :=
  ∀ q, |a q - roughMangoldtWeight y q| ≤ δ * |roughMangoldtWeight y q|

private theorem relative_displacement (y X T : ℕ) {a : ArithmeticFunction ℝ} {δ : ℝ}
    (box : insideRelativeBox y δ a) :
    |roughInteriorReading a y X T - roughInteriorReading (roughMangoldtWeight y) y X T| ≤
      δ * absoluteRoughInterior y X T := by
  simp only [rough_interior_as_kernel, ← sum_sub_distrib, absoluteRoughInterior, mul_sum]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro q _
  rw [← sub_mul, abs_mul, abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (box q) (abs_nonneg _)

private theorem aligned_shift (y X T : ℕ) (s : ℝ) :
    ∃ a : ArithmeticFunction ℝ, insideRelativeBox y |s| a ∧
      roughInteriorReading a y X T = roughInteriorReading (roughMangoldtWeight y) y X T +
        s * absoluteRoughInterior y X T := by
  let w := roughMangoldtWeight y
  let v := roughRestriction y (aligned y X T)
  let a : ArithmeticFunction ℝ := ⟨fun q => w q + s*v q, by simp⟩
  have habs (q : ℕ) : |v q| = |w q| := by
    dsimp only [v,w,roughMangoldtWeight]
    rw [roughRestriction_apply,roughRestriction_apply]
    split_ifs
    · change |if _ then vonMangoldt q else -vonMangoldt q|=_
      split <;> simp only [abs_neg]
    · rfl
  refine ⟨a,fun q => ?_,?_⟩
  · change |w q+s*v q-w q| ≤ |s| * |w q|
    rw [add_sub_cancel_left,abs_mul,habs]
  · rw [aligned_eq,rough_interior_as_kernel,rough_interior_as_kernel,rough_interior_as_kernel,
      mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro q _
    change (w q+s*v q)*_=w q*_+s*(v q*_)
    ring

/-- The largest absolute reading under a relative perturbation is attained.
Both signs can be chosen independently at each surviving prime power. -/
theorem extremal_magnitude_in_relative_box (y X T : ℕ) {δ : ℝ} (hd : 0 ≤ δ) :
    IsGreatest {z : ℝ | ∃ a : ArithmeticFunction ℝ, insideRelativeBox y δ a ∧
      z = |roughInteriorReading a y X T|}
      (|roughInteriorReading (roughMangoldtWeight y) y X T| + δ*absoluteRoughInterior y X T) := by
  let S := roughInteriorReading (roughMangoldtWeight y) y X T
  let V := absoluteRoughInterior y X T
  have vp : 0 ≤ V := sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · by_cases pos : 0 ≤ S
    · obtain ⟨a,box,h⟩ := aligned_shift y X T δ
      refine ⟨a,by simpa only [abs_of_nonneg hd] using box,?_⟩
      rw [h,abs_of_nonneg pos,abs_of_nonneg (add_nonneg pos (mul_nonneg hd vp))]
    · obtain ⟨a,box,h⟩ := aligned_shift y X T (-δ)
      have neg := le_of_not_ge pos
      refine ⟨a,by simpa only [abs_neg,abs_of_nonneg hd] using box,?_⟩
      rw [h,abs_of_nonpos neg,abs_of_nonpos (add_nonpos neg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) vp))]
      ring
  · rintro z ⟨a,box,rfl⟩
    have h := abs_add_le S (roughInteriorReading a y X T-S)
    rw [show S+(roughInteriorReading a y X T-S)=roughInteriorReading a y X T by ring] at h
    exact h.trans (add_le_add le_rfl (relative_displacement y X T box))

/-- The relative tolerance required to make a signed reading zero is
exactly the ratio of its magnitude to the absolute row mass. -/
theorem zero_attained_in_relative_box (y X T : ℕ) {δ : ℝ}
    (hv : 0 < absoluteRoughInterior y X T) :
    (∃ a : ArithmeticFunction ℝ, insideRelativeBox y δ a ∧ roughInteriorReading a y X T=0) ↔
      |roughInteriorReading (roughMangoldtWeight y) y X T| / absoluteRoughInterior y X T ≤ δ := by
  let S := roughInteriorReading (roughMangoldtWeight y) y X T
  let V := absoluteRoughInterior y X T
  constructor
  · rintro ⟨a,ha,hzero⟩
    have hb := relative_displacement y X T ha
    rw [hzero,zero_sub,abs_neg] at hb
    exact (div_le_iff₀ hv).mpr hb
  · intro h
    obtain ⟨a,ha,hval⟩ := aligned_shift y X T (-S/V)
    have hs : |(-S)/V| ≤ δ := by rw [abs_div,abs_neg,abs_of_pos hv]; exact h
    refine ⟨a,fun q => (ha q).trans (mul_le_mul_of_nonneg_right hs (abs_nonneg _)),?_⟩
    change _ = S+(-S/V)*V at hval
    rwa [div_mul_cancel₀ _ hv.ne', add_neg_cancel] at hval

private def cap (f : ℕ → ℝ) (u : ℝ) :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, |f X| ≤ C*(X:ℝ)^u

private theorem caps_of_close {f g : ℕ → ℝ} {u K : ℝ} (hk : 0 ≤ K)
    (close : ∀ᶠ n : ℕ in atTop, |f n-g n| ≤ K*(n:ℝ)^u) :
    cap f u ↔ cap g u := by
  have transfer {f g : ℕ → ℝ} (hfg : ∀ᶠ n : ℕ in atTop, |f n-g n| ≤ K*(n:ℝ)^u)
      (hf : cap f u) : cap g u := by
    obtain ⟨C,hC,hh⟩ := hf
    refine ⟨C+K,add_nonneg hC hk,?_⟩
    filter_upwards [hfg,hh] with n diff price
    have tri := abs_sub (f n) (f n-g n)
    rw [sub_sub_cancel] at tri
    exact tri.trans ((add_le_add price diff).trans_eq (by ring))
  exact ⟨transfer close, transfer (close.mono fun n h => by simpa only [abs_sub_comm (g n)] using h)⟩

/-- The literal signed four-sevenths sum detects each strip exponent above
one half. Removing the head costs strictly less than the square-root power. -/
theorem signed_four_sevenths_detects_each_strip {β : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop,
      |primePowerInteriorAtExponent (4/7) X| ≤ C*(X:ℝ)^(β+ε)) ↔ _root_.RHTower.zetaZeroAbscissa ≤ β := by
  let g := terminalMangoldtHead 1
  have full (X : ℕ) : g X = roughCofactorReading (logSquareCutoff X) X
      (quotientReading (roughMangoldtWeight (logSquareCutoff X))) := by
    simp only [g, terminalMangoldtHead, terminalPrimeHead, Real.rpow_one, Nat.floor_natCast,
      rough_action_as_a_coefficient_prefix, roughFloorCoefficient]
  have g0 : g 0 = 0 := by simp [g,terminalMangoldtHead,terminalPrimeHead,quotientReading]
  have compare {ε : ℝ} (he : 0 < ε) : cap signed (β+ε) ↔ PrefixPower (β+ε) g := by
    obtain ⟨K,hK,h⟩ := ordinary_and_prime_power_transfer_to_three_sevenths
    have close : ∀ᶠ X : ℕ in atTop, |g X-signed X| ≤ K*(X:ℝ)^(β+ε) := by
      filter_upwards [h,eventually_ge_atTop 1] with X hx hp
      let y := logSquareCutoff X
      have h' := hx.2 (roughMangoldtWeight y) (by simp [y])
      rw [full]
      exact h'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        ((Nat.one_le_cast (α:=ℝ)).mpr hp) (by linarith only [he,hb] : (1:ℝ)/2-1/84000 ≤ β+ε)) hK)
    have bridge := caps_of_close hK close
    constructor
    · intro h
      obtain ⟨C,_,h⟩ := bridge.mpr h
      exact prefixPower_of_eventual g0 (by linarith only [he,hb]) h
    · rintro ⟨C,hC,h⟩
      exact bridge.mp ⟨C,hC,Eventually.of_forall h⟩
  have ht := terminal_mangoldt_head_detects_the_strip (α:=1) (by norm_num) le_rfl hb
  simp only [one_mul] at ht
  exact ⟨fun h => ht.mp fun ε he => (compare he).mp (h ε he),
    fun h ε he => (compare he).mpr (ht.mpr h ε he)⟩

/-- Magnitude of the arithmetic reading divided by its exact coordinatewise
relative-error norm. This is the size of a relative perturbation which
can make the reading vanish when its absolute mass is positive. -/
def fourSeventhsRelativeSignRadius (X : ℕ) := |signed X| / mass X

private theorem mass_power {η : ℝ} (he : 0 < η) :
    ∀ᶠ X : ℕ in atTop, (X:ℝ) ≤ mass X ∧ mass X ≤ (X:ℝ)^(1+η) := by
  filter_upwards [absolute_price_at_four_sevenths (ε:=1) zero_lt_one,
    absolute_rough_mass_saves_at_growing_walls _ logSquareCutoff_tendsto_atTop (δ:=1) zero_lt_one,
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (_root_.RHTower.burnolEventually_log_pow_le_rpow he 1),
    eventually_ge_atTop 1] with X lower upper logPrice xp
  have hlog : Real.log X ≤ (X:ℝ)^η := by simpa using logPrice
  have hi := upper (cut X)
  simp only [one_mul] at hi
  rw [Real.rpow_add (Nat.cast_pos.mpr xp),Real.rpow_one]
  exact ⟨by simpa only [sub_self,show (2:ℝ)-1=1 by norm_num,one_mul] using lower,
    hi.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))⟩

/-- The relative sign radius has upper power exponent Θ−1. At β=1/2
its square-root decay up to subpower factors is equivalent to the critical strip bound. -/
theorem sign_radius_detects_the_zero_abscissa {β : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop,
      fourSeventhsRelativeSignRadius X ≤ C*(X:ℝ)^(β-1+ε)) ↔ _root_.RHTower.zetaZeroAbscissa ≤ β := by
  rw [← signed_four_sevenths_detects_each_strip hb]
  constructor
  · intro h ε he
    obtain ⟨C,hC,cap⟩ := h (ε/2) (half_pos he)
    refine ⟨C,hC,?_⟩
    filter_upwards [cap,mass_power (half_pos he),eventually_ge_atTop 1] with X hh hm hx
    have hp : 0 < (X:ℝ) := Nat.cast_pos.mpr hx
    have h1 := (div_le_iff₀ (hp.trans_le hm.1)).mp hh
    apply h1.trans ((mul_le_mul_of_nonneg_left hm.2 (mul_nonneg hC (Real.rpow_nonneg hp.le _))).trans_eq ?_)
    rw [mul_assoc,← Real.rpow_add hp,show β-1+ε/2+(1+ε/2)=β+ε by ring]
  · intro h ε he
    obtain ⟨C,hC,cap⟩ := h ε he
    refine ⟨C,hC,?_⟩
    filter_upwards [cap,mass_power he,eventually_ge_atTop 1] with X hh hm hx
    have hp : 0 < (X:ℝ) := Nat.cast_pos.mpr hx
    apply (div_le_iff₀ (hp.trans_le hm.1)).mpr
    apply hh.trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hm.1 (mul_nonneg hC (Real.rpow_nonneg hp.le _))))
    calc C * (X:ℝ)^(β+ε) = C * ((X:ℝ)^(β-1+ε) * (X:ℝ)^(1:ℝ)) := by
           rw [← Real.rpow_add hp, show β-1+ε+1=β+ε by ring]
         _ = _ := by rw [Real.rpow_one, mul_assoc]

/-- The upper exponent under independent coordinate errors of size X^(−γ)
is the larger of the zeta zero abscissa and 1−γ. This includes errors in
ordinary prime increments as well as in the proper prime powers. -/
theorem relative_perturbation_power_threshold {β γ : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ a : ArithmeticFunction ℝ,
      insideRelativeBox (logSquareCutoff X) ((X:ℝ)^(-γ)) a →
      |roughInteriorReading a (logSquareCutoff X) X (cut X)| ≤ C*(X:ℝ)^(β+ε)) ↔
      max _root_.RHTower.zetaZeroAbscissa (1-γ) ≤ β := by
  constructor
  · intro all
    apply max_le
    · apply (signed_four_sevenths_detects_each_strip hb).mp
      intro ε he
      obtain ⟨C,hC,cap⟩ := all ε he
      refine ⟨C,hC,cap.mono fun X h => ?_⟩
      apply h (roughMangoldtWeight (logSquareCutoff X))
      intro q
      rw [sub_self,abs_zero]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg _)
    · by_contra! gap
      let η := (1-γ-β)/2
      have he : 0 < η := half_pos (sub_pos.mpr gap)
      obtain ⟨C,hC,cap⟩ := all η he
      have grow := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
      obtain ⟨X,allX,massX,hgrow,hx⟩ := (cap.and ((mass_power he).and
        ((grow.eventually_gt_atTop C).and (eventually_ge_atTop 1)))).exists
      have xp : 0 < (X:ℝ) := Nat.cast_pos.mpr hx
      let y := logSquareCutoff X
      have dp := Real.rpow_nonneg xp.le (-γ)
      obtain ⟨a,ha,hm⟩ := (extremal_magnitude_in_relative_box y X (cut X) dp).1
      have lower := mul_le_mul_of_nonneg_left massX.1 dp
      have paid : (X:ℝ)^(-γ)*(X:ℝ) ≤ C*(X:ℝ)^(β+η) :=
        lower.trans ((le_add_of_nonneg_left (abs_nonneg _)).trans (hm.le.trans (allX a ha)))
      have eq : (X:ℝ)^(-γ)*(X:ℝ) = (X:ℝ)^η*(X:ℝ)^(β+η) := by
        calc _ = (X:ℝ)^(-γ)*(X:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
             _ = _ := by rw [← Real.rpow_add xp,← Real.rpow_add xp]; congr 1; dsimp only [η]; ring
      rw [eq] at paid
      exact ((mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos xp (β+η))).mp paid).not_gt hgrow
  · intro both ε he
    obtain ⟨C,hC,cap⟩ := (signed_four_sevenths_detects_each_strip hb).mpr
      ((le_max_left ..).trans both) ε he
    refine ⟨C+1,add_nonneg hC zero_le_one,?_⟩
    filter_upwards [cap,mass_power he,eventually_ge_atTop 1] with X paid hm hx
    intro a ha
    let y := logSquareCutoff X
    have xp : 0 < (X:ℝ) := Nat.cast_pos.mpr hx
    have dp := Real.rpow_nonneg xp.le (-γ)
    have price := (extremal_magnitude_in_relative_box y X (cut X) dp).2
      (show |roughInteriorReading a y X (cut X)| ∈ _ from ⟨a,ha,rfl⟩)
    have err := mul_le_mul_of_nonneg_left hm.2 dp
    rw [← Real.rpow_add xp] at err
    have expo : -γ+(1+ε) ≤ β+ε := by linarith only [(le_max_right ..).trans both]
    have hnoise := err.trans (Real.rpow_le_rpow_of_exponent_le ((Nat.one_le_cast (α:=ℝ)).mpr hx) expo)
    exact price.trans ((add_le_add paid hnoise).trans_eq (by ring))

end GaloisForLFunctions.RestrictedFactorizationCalculus
