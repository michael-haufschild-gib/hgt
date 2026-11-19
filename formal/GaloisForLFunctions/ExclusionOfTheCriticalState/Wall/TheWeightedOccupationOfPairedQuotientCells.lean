import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSquareChargeInsideTheDiagonalInterval

/-!
# Weighted occupation of paired quotient intervals

A common interval of numerators cuts out one interval of log numerators.
The confined state gives bounded total density over all binary lifts of any
such region. The resulting estimate applies directly to the original test
with its moving prime band, including on subsets selected by orientation.
-/

noncomputable section
open scoped Classical
open Set MeasureTheory Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry

/-- An integer interval and its specified quotient. -/
structure QuotientCell where
  lower : ℕ
  upper : ℕ
  quotient : ℕ

/-- The quotient is constant on the entire rectangle of numerators and denominators. -/
def QuotientCell.holds (c : QuotientCell) (H D : ℕ) : Prop :=
  D≤H ∧ ∀ j ∈ Finset.Icc (H-D) H, ∀ n ∈ Finset.Ioc c.lower c.upper, j/n=c.quotient

theorem QuotientCell.holds_iff (c : QuotientCell) (hc : c.lower<c.upper) (H D : ℕ) :
    c.holds H D ↔ D+c.quotient*c.upper≤H ∧ H<(c.quotient+1)*(c.lower+1) := by
  have hpos : 0<c.upper := Nat.zero_lt_of_lt hc
  constructor
  · rintro ⟨hd,h⟩
    have hm := h (H-D) (Finset.mem_Icc.mpr ⟨le_rfl,Nat.sub_le ..⟩) c.upper (Finset.mem_Ioc.mpr ⟨hc,le_rfl⟩)
    have ht := h H (Finset.mem_Icc.mpr ⟨Nat.sub_le ..,le_rfl⟩) (c.lower+1) (Finset.mem_Ioc.mpr ⟨Nat.lt_succ_self _,hc⟩)
    have hl := (Nat.le_div_iff_mul_le hpos).mp hm.ge
    exact ⟨by omega,(Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ _)).mp (ht.trans_lt (Nat.lt_succ_self _))⟩
  · rintro ⟨hl,hr⟩
    refine ⟨by omega,fun j hj n hn => ?_⟩
    obtain ⟨hm,hjH⟩ := Finset.mem_Icc.mp hj
    obtain ⟨hn₁,hn₂⟩ := Finset.mem_Ioc.mp hn
    have hn0 : 0<n := Nat.zero_lt_of_lt hn₁
    apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hn0).mpr
        (hjH.trans_lt (hr.trans_le (Nat.mul_le_mul_left _ hn₁))))
    · exact (Nat.le_div_iff_mul_le hn0).mpr ((Nat.mul_le_mul_left _ hn₂).trans (by omega))

/-- Inclusive lower and exclusive upper endpoints of the common numerator range. -/
def pairNumeratorStart (a b : QuotientCell) (D : ℕ) :=
  D+max (a.quotient*a.upper) (b.quotient*b.upper)

def pairNumeratorStop (a b : QuotientCell) :=
  min ((a.quotient+1)*(a.lower+1)) ((b.quotient+1)*(b.lower+1))

theorem pairedQuotients_hold_iff (a b : QuotientCell) (ha : a.lower<a.upper) (hb : b.lower<b.upper)
    (H D : ℕ) : a.holds H D ∧ b.holds H D ↔
      pairNumeratorStart a b D≤H ∧ H<pairNumeratorStop a b := by
  rw [a.holds_iff ha,b.holds_iff hb]
  dsimp only [pairNumeratorStart,pairNumeratorStop]; omega

private def digitLevel (T : ℝ) (j : ℕ) : ℝ := T+(j+1:ℕ)*Real.log 2

/-- Displacements for which some binary digit hits the specified region of log numerators. -/
def hitsLogNumerators (T : ℝ) (W : Set ℝ) : Set ℝ :=
  {v | ∃ j : ℕ, digitLevel T j-v∈W}

theorem measurableSet_hitsLogNumerators (T : ℝ) {W : Set ℝ} (hW : MeasurableSet W) :
    MeasurableSet (hitsLogNumerators T W) := by
  change MeasurableSet {v : ℝ | ∃ j : ℕ, digitLevel T j-v∈W}
  rw [setOf_exists]; exact MeasurableSet.iUnion fun j => hW.preimage (measurable_const.sub measurable_id)

/-- The logarithmic region is equivalent to simultaneous occurrence at the
same binary digit of the actual fractional numerator. -/
theorem hitsLogNumerators_pair_iff (a b : QuotientCell) (ha : a.lower<a.upper) (hb : b.lower<b.upper)
    (hq : 0<a.quotient) (D : ℕ) (T v : ℝ) :
    v∈hitsLogNumerators T (Ico (Real.log (pairNumeratorStart a b D)) (Real.log (pairNumeratorStop a b))) ↔
      ∃ j : ℕ, let H := ⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊
        a.holds H D ∧ b.holds H D := by
  have hA : 0<(pairNumeratorStart a b D:ℝ) := by
    apply Nat.cast_pos.mpr
    exact (mul_pos hq (Nat.zero_lt_of_lt ha)).trans_le
      ((le_max_left ..).trans (Nat.le_add_left ..))
  have hB : 0<(pairNumeratorStop a b:ℝ) := Nat.cast_pos.mpr (lt_min (by positivity) (by positivity))
  apply exists_congr
  intro j
  let z := digitLevel T j-v
  have he : Real.exp z=(2:ℝ)^(j+1)*Real.exp (T-v) := by
    rw [show z=((j+1:ℕ):ℝ)*Real.log 2+(T-v) by dsimp [z,digitLevel]; ring,Real.exp_add,Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [pairedQuotients_hold_iff a b ha hb,← he]
  change Real.log (pairNumeratorStart a b D)≤z ∧ z<Real.log (pairNumeratorStop a b) ↔ _
  rw [Real.log_le_iff_le_exp hA,Real.lt_log_iff_exp_lt hB,Nat.le_floor_iff (Real.exp_pos z).le,
    Nat.floor_lt (Real.exp_pos z).le]

private def wallDensity (v : ℝ) : ℝ := if v≤0 then Real.exp v else 0
private def cappedExp (v : ℝ) : ℝ := min 1 (Real.exp v)

private theorem density_bounds (v : ℝ) : 0≤wallDensity v ∧ wallDensity v≤1 := by
  by_cases h : v≤0 <;> simp only [wallDensity,h,if_true,if_false]
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr h⟩
  · exact ⟨le_rfl,zero_le_one⟩

private theorem measurable_density : Measurable wallDensity :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) Real.measurable_exp measurable_const

/-- A backward difference of the capped exponential dominates the density.
The finite sum over all translates telescopes, independently of the number of digits. -/
private theorem sum_binary_density (T z : ℝ) (J : ℕ) :
    ∑ j ∈ Finset.range J, wallDensity (digitLevel T j-z) ≤ 2 := by
  let p := fun j : ℕ => T+(j:ℝ)*Real.log 2-z
  have hstep (j : ℕ) : p (j+1)=p j+Real.log 2 := by dsimp only [p]; push_cast; ring
  have hinc (j : ℕ) : p j≤p (j+1) := by rw [hstep]; linarith only [Real.log_nonneg (by norm_num : (1:ℝ)≤2)]
  have hterm (j : ℕ) : wallDensity (digitLevel T j-z)≤2*(cappedExp (p (j+1))-cappedExp (p j)) := by
    change wallDensity (p (j+1))≤_
    by_cases h : p (j+1)≤0
    · rw [wallDensity,if_pos h,cappedExp,cappedExp,min_eq_right (Real.exp_le_one_iff.mpr h),
        min_eq_right (Real.exp_le_one_iff.mpr ((hinc j).trans h)),hstep,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
      exact le_of_eq (by ring)
    · rw [wallDensity,if_neg h]
      exact mul_nonneg (by norm_num) (sub_nonneg.mpr (min_le_min_left _ (Real.exp_le_exp.mpr (hinc j))))
  have h := Finset.sum_le_sum (s := Finset.range J) fun j _ => hterm j
  rw [← Finset.mul_sum,Finset.sum_range_sub (fun j => cappedExp (p j))] at h
  exact h.trans (by have ha : cappedExp (p J)≤1 := min_le_left ..; have hb : 0≤cappedExp (p 0) := le_min zero_le_one (Real.exp_pos _).le; linarith only [ha,hb])

private theorem last_digit (T U : ℝ) : ∃ J : ℕ, ∀ j, J≤j → U<digitLevel T j := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨J,hJ⟩ := exists_nat_gt ((U-T)/Real.log 2)
  refine ⟨J,fun j hj => ?_⟩
  have h := (div_lt_iff₀ hlog).mp (hJ.trans_le
    (Nat.cast_le.mpr (hj.trans (Nat.le_succ j)) : (J:ℝ)≤(j+1:ℕ)))
  dsimp only [digitLevel]; linarith only [h]

private theorem displacement_integrable {Φ : ℝ → ℝ} (hi : Integrable Φ) (hs : ∀ v, 0≤v → Φ v=0)
    {E : Set ℝ} (hm : MeasurableSet E) :
    Integrable (fun v : ℝ => Real.exp (v/2)*|E.indicator Φ v|) := by
  have h := hi.indicator hm
  apply h.abs.mono' ((by fun_prop : Measurable (fun v : ℝ => Real.exp (v/2))).aestronglyMeasurable.mul h.abs.aestronglyMeasurable)
  filter_upwards [] with v
  change ‖Real.exp (v/2)*|E.indicator Φ v|‖ ≤ |E.indicator Φ v|
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
  by_cases hv : v≤0
  · exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr (by linarith only [hv]))
  · by_cases he : v∈E <;> simp [he,hs v (le_of_not_ge hv)]

/-- The actual confined state, summed over every admissible binary lift,
puts at most twice its confinement constant times length on log numerators. -/
theorem weighted_occupation_log_numerators {Φ : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hs : ∀ v, 0≤v → Φ v=0) (hb : ∀ v, |Φ v|≤C*Real.exp (2*v))
    (hiΦ : Integrable Φ) (T : ℝ) {W E : Set ℝ} (hmE : MeasurableSet E) (hW : MeasurableSet W) (hfin : volume W≠⊤)
    (hU : BddAbove W) (hE : E ⊆ hitsLogNumerators T W) :
    (∫ v, Real.exp (v/2)*|E.indicator Φ v|) ≤ 2*C*volume.real W := by
  obtain ⟨U,hU⟩ := hU
  obtain ⟨J,hJ⟩ := last_digit T U
  let f := fun (j : ℕ) => W.indicator (fun z : ℝ => wallDensity (digitLevel T j-z))
  have hconst (A : ℝ) : Integrable (W.indicator fun _ : ℝ => A) :=
    (integrableOn_const (hs := hfin)).integrable_indicator hW
  have hi (j : ℕ) : Integrable (f j) := by
    apply (hconst 1).mono' ((measurable_density.comp (measurable_const.sub measurable_id)).indicator hW).aestronglyMeasurable
    filter_upwards [] with z
    change ‖f j z‖ ≤ W.indicator (fun _ : ℝ => (1:ℝ)) z
    by_cases hz : z∈W
    · simp only [f,indicator_of_mem hz,Real.norm_eq_abs,abs_of_nonneg (density_bounds _).1]
      exact (density_bounds _).2
    · simp [f,hz]
  have hpos (j : ℕ) (z : ℝ) : 0≤f j z := indicator_nonneg (fun x _ => (density_bounds _).1) z
  let g := fun (v : ℝ) => ∑ j ∈ Finset.range J, f j (digitLevel T j-v)
  have hg : Integrable g := integrable_finsetSum _ (fun j _ => (hi j).comp_sub_left _)
  have hbound (v : ℝ) : Real.exp (v/2)*|E.indicator Φ v| ≤ C*g v := by
    have hn : 0≤C*g v := mul_nonneg hC (Finset.sum_nonneg (fun j _ => hpos j _))
    by_cases hv : v∈E
    · rw [indicator_of_mem hv]
      by_cases hnegative : v≤0
      · obtain ⟨j,hj⟩ := hE hv
        have hlt : j<J := by
          by_contra! h
          have h₁ := hJ j h
          have h₂ := hU hj
          linarith only [hnegative,h₁,h₂]
        have hsingle := Finset.single_le_sum (s := Finset.range J)
          (f := fun i => f i (digitLevel T i-v)) (fun i _ => hpos i _) (Finset.mem_range.mpr hlt)
        have henv : Real.exp v≤g v := by
          simpa only [f,g,indicator_of_mem hj,sub_sub_cancel,wallDensity,if_pos hnegative] using hsingle
        have hsmall := Real.exp_le_exp.mpr (by linarith only [hnegative] : 2*v≤v)
        calc _ ≤ 1*(C*Real.exp (2*v)) := mul_le_mul (Real.exp_le_one_iff.mpr (by linarith only [hnegative]))
                    (hb v) (abs_nonneg _) zero_le_one
             _ ≤ _ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left (hsmall.trans henv) hC
      · rw [hs v (le_of_not_ge hnegative),abs_zero,mul_zero]; exact hn
    · rw [indicator_of_notMem hv,abs_zero,mul_zero]; exact hn
  have hfold (z : ℝ) : ∑ j ∈ Finset.range J, f j z ≤ W.indicator (fun _ => (2:ℝ)) z := by
    by_cases hz : z∈W
    · simp only [f,indicator_of_mem hz]; exact sum_binary_density T z J
    · simp [f,hz]
  have hmass := integral_mono (integrable_finsetSum _ (fun j _ => hi j)) (hconst 2) hfold
  rw [integral_indicator hW,setIntegral_const,smul_eq_mul] at hmass
  have hchange : (∫ v, g v)=∫ z, ∑ j ∈ Finset.range J, f j z := by
    rw [show g=(fun v => ∑ j ∈ Finset.range J, f j (digitLevel T j-v)) from rfl,
      integral_finsetSum _ (fun j _ => (hi j).comp_sub_left _),integral_finsetSum _ (fun j _ => hi j)]
    exact Finset.sum_congr rfl (fun j _ => integral_sub_left_eq_self (f j) volume _)
  have h := integral_mono (displacement_integrable hiΦ hs hmE) (hg.const_mul C) hbound
  rw [integral_const_mul,hchange] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hmass hC).trans_eq (by ring))

private abbrev coeff (n : ℕ) : ℝ := (if n.Prime then vonMangoldt n else 0)-1

private theorem ordinary_mass (k L : ℕ) :
    (∑ n ∈ Finset.Ioc k L, |coeff n|) ≤ (1+Real.log 4)*L := by
  let w := fun n : ℕ => (if n.Prime then Real.log n else 0)+1
  have hnn (n : ℕ) : 0≤(if n.Prime then Real.log n else 0) := by
    split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
  have hb (n : ℕ) : |coeff n|≤w n := by
    have he : coeff n=(if n.Prime then Real.log n else 0)-1 := by
      by_cases hp : n.Prime <;> simp [coeff,hp,vonMangoldt_apply_prime]
    rw [he]
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hnn n),abs_one])
  have hsub : Finset.Ioc k L ⊆ Finset.Ioc 0 L := fun n hn => Finset.mem_Ioc.mpr
    ⟨Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2⟩
  have hsum : (∑ n ∈ Finset.Ioc 0 L, w n)=Chebyshev.theta L+L := by
    simp only [w,Finset.sum_add_distrib,Chebyshev.theta,Nat.floor_natCast,Finset.sum_filter,
      Finset.sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one]
  calc _ ≤ ∑ n ∈ Finset.Ioc k L, w n := Finset.sum_le_sum fun n _ => hb n
       _ ≤ ∑ n ∈ Finset.Ioc 0 L, w n := Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (fun n _ _ => add_nonneg (hnn n) zero_le_one)
       _ ≤ _ := by rw [hsum]; linarith only [Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg L)]

private theorem atom_price (Φ : ℝ → ℝ) {n : ℕ} (hn : 0<n) (T t : ℝ) :
    |continuousIntegerAtom Φ n t*fractionalPrimeTest (T-t)| ≤
      Real.exp (-T/2)*(Real.exp ((t-Real.log n)/2)*|Φ (t-Real.log n)|) := by
  have ha : (Real.sqrt (n:ℝ))⁻¹=Real.exp (-(Real.log n)/2) := by
    rw [neg_div,Real.exp_neg,Real.exp_half,Real.exp_log (Nat.cast_pos.mpr hn)]
  have hex : Real.exp (-(Real.log n)/2)*Real.exp (-(T-t)/2)=Real.exp (-T/2)*Real.exp ((t-Real.log n)/2) := by
    rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  calc _ = (Real.exp (-T/2)*(Real.exp ((t-Real.log n)/2)*|Φ (t-Real.log n)|))*Int.fract (Real.exp (T-t)) := by
            simp only [continuousIntegerAtom,fractionalPrimeTest,ha,abs_mul,abs_of_pos (Real.exp_pos _),
              abs_of_nonneg (Int.fract_nonneg (Real.exp (T-t)))]
            linear_combination (|Φ (t-Real.log n)| *Int.fract (Real.exp (T-t)))*hex
       _ ≤ _ := mul_le_of_le_one_right (by positivity) (Int.fract_lt_one _).le

/-- The restricted profile masks only the actual atom displacement. The
integral of the original state remains the orienting multiplier. The time set
may in particular be the middle test or either part of a good/bad split. -/
theorem criticalState_ordinaryBand_occupation {W₀ : ℝ} (hW₀ : 0<W₀)
    (ht : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (T : ℝ) (k L : ℕ) (A W E : Set ℝ), MeasurableSet W → volume W≠⊤ →
      BddAbove W → MeasurableSet E → E ⊆ hitsLogNumerators T W →
      (∫ t in A, |(∫ v, Φ v)*ordinaryPrimeComplementBand (E.indicator Φ) k L t*fractionalPrimeTest (T-t)|)
        ≤ K*L*Real.exp (-T/2)*volume.real W := by
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hbound⟩,_⟩ := criticalState_exists_continuous_representative hW₀ ht hF
  have hsame := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  have hi := ((criticalHalfLineEnergyDomain_of_groundState hF).integrable).congr he
  let m := ∫ v, Φ v
  refine ⟨2*C*|m| *(1+Real.log 4),by positivity,fun T k L A W E hW hf hU hE hV => ?_⟩
  let w := fun v : ℝ => Real.exp (v/2)*|E.indicator Φ v|
  have hw : Integrable w := displacement_integrable hi hs hE
  have hmass := weighted_occupation_log_numerators hC hs hbound hi T hE hW hf hU hV
  let kappa := Real.exp (-T/2)
  let g := fun (n : ℕ) (t : ℝ) => (|coeff n| *kappa)*w (t-Real.log n)
  let S := Finset.Ioc k L
  have hg (n : ℕ) : Integrable (g n) := (hw.comp_sub_right _).const_mul _
  have hnn (n : ℕ) (t : ℝ) : 0≤g n t := by dsimp only [g,kappa,w]; positivity
  let G := fun t : ℝ => ∑ n ∈ S, g n t
  have hG : Integrable G := integrable_finsetSum _ (fun n _ => hg n)
  let read := fun t : ℝ => ordinaryPrimeComplementBand (E.indicator Φ) k L t*fractionalPrimeTest (T-t)
  have hread (t : ℝ) : |read t|≤G t := by
    dsimp only [read,ordinaryPrimeComplementBand,G,S]
    rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    by_cases h : pastCriticalEdge n t
    · rw [if_pos h,mul_assoc,abs_mul]
      exact (mul_le_mul_of_nonneg_left (atom_price _ (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1) T t)
        (abs_nonneg (coeff n))).trans_eq (by dsimp only [g,kappa,w]; ring)
    · rw [if_neg h,zero_mul,abs_zero]; exact hnn _ _
  have hmeas : Measurable read := by
    apply Measurable.mul _ (measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id))
    apply Finset.measurable_fun_sum
    intro n _
    apply Measurable.ite (measurableSet_lt (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const)
    · exact measurable_const.mul (measurable_const.mul ((hc.measurable.indicator hE).comp (measurable_id.sub measurable_const)))
    · exact measurable_const
  have hri : Integrable read := hG.mono' hmeas.aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hread t)
  have hpoint (t : ℝ) : |m*read t|≤|m| *G t := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hread _) (abs_nonneg _)
  have hGG := hG.const_mul |m|
  have hboundA := (integral_mono ((hri.const_mul m).abs.integrableOn (s := A)) hGG.integrableOn hpoint).trans
    (setIntegral_le_integral hGG (Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun n _ => hnn n t))))
  have hgj (n : ℕ) : (∫ t, g n t)=(|coeff n| *kappa)*(∫ v, w v) := by
    dsimp only [g]; rw [integral_const_mul,integral_sub_right_eq_self]
  have hGI : (∫ t, G t)=(∑ n ∈ S, |coeff n|)*kappa*(∫ v, w v) := by
    dsimp only [G]; rw [integral_finsetSum _ (fun n _ => hg n)]; simp_rw [hgj]
    rw [← Finset.sum_mul,← Finset.sum_mul]
  rw [integral_const_mul,hGI] at hboundA
  change (∫ t in A, |m*ordinaryPrimeComplementBand (E.indicator Φ) k L t*fractionalPrimeTest (T-t)|) ≤ _
  simp_rw [mul_assoc m]
  change (∫ t in A, |m*read t|) ≤ _
  apply hboundA.trans
  have hwpos : 0≤∫ v, w v := integral_nonneg fun v => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_right (ordinary_mass k L) (Real.exp_pos (-T/2)).le)
    hmass hwpos (by positivity)
  exact (mul_le_mul_of_nonneg_left hprod (abs_nonneg m)).trans_eq (by ring)

/-- Removing the selected displacements subtracts precisely their response
from the original band, before taking any absolute value or time integral. -/
theorem ordinaryBand_sub_remove_displacements (Φ : ℝ → ℝ) (E : Set ℝ) (k L : ℕ) (t : ℝ) :
    ordinaryPrimeComplementBand Φ k L t-ordinaryPrimeComplementBand (Eᶜ.indicator Φ) k L t =
      ordinaryPrimeComplementBand (E.indicator Φ) k L t := by
  unfold ordinaryPrimeComplementBand
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : pastCriticalEdge n t <;> by_cases he : t-Real.log n∈E <;>
    simp [h,he,continuousIntegerAtom]

/-- Joint occupation at the original state orientation, with the common
numerator range shortened by the full terminal block width. -/
theorem criticalState_paired_cell_occupation {W₀ : ℝ} (hW₀ : 0<W₀)
    (ht : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (T s : ℝ) (k L D : ℕ) (A : Set ℝ) (a b : QuotientCell),
      a.lower<a.upper → b.lower<b.upper → a.quotient%2=1 → b.quotient%2=1 →
      let m := ∫ v, Φ v
      let E := {v : ℝ | s*m*Φ v<0 ∧ ∃ j : ℕ, let H := ⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊
        a.holds H D ∧ b.holds H D}
      (∫ t in A, |m*(ordinaryPrimeComplementBand Φ k L t-ordinaryPrimeComplementBand (Eᶜ.indicator Φ) k L t)*
        fractionalPrimeTest (T-t)|) ≤ K*L*Real.exp (-T/2)*
          max (Real.log (pairNumeratorStop a b)-Real.log (pairNumeratorStart a b D)) 0 := by
  obtain ⟨K,hK,h⟩ := criticalState_ordinaryBand_occupation hW₀ ht hF hc he
  refine ⟨K,hK,fun T s k L D A a b ha hb hq _ => ?_⟩
  let W := Ico (Real.log (pairNumeratorStart a b D)) (Real.log (pairNumeratorStop a b))
  let m := ∫ v, Φ v
  let E := {v : ℝ | s*m*Φ v<0} ∩ hitsLogNumerators T W
  have hq₀ : 0<a.quotient := Nat.pos_of_ne_zero (fun hz => by simp [hz] at hq)
  have hset : {v : ℝ | s*m*Φ v<0 ∧ ∃ j : ℕ, let H := ⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊
      a.holds H D ∧ b.holds H D}=E := by
    ext v; exact and_congr_right fun _ => (hitsLogNumerators_pair_iff a b ha hb hq₀ D T v).symm
  have hE : MeasurableSet E := (measurableSet_lt (measurable_const.mul hc.measurable) measurable_const).inter
    (measurableSet_hitsLogNumerators _ measurableSet_Ico)
  have hmeasure : volume W≠⊤ := by rw [show W=Ico _ _ from rfl,Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  have hbdd : BddAbove W := ⟨_,fun z hz => hz.2.le⟩
  dsimp only
  rw [hset]
  simp_rw [ordinaryBand_sub_remove_displacements]
  simpa only [W,Real.volume_real_Ico] using h T k L A W E measurableSet_Ico hmeasure hbdd hE inter_subset_right

/-- The log measure of a finite list of positive integer numerators is at
most their reciprocal sum. Repeated incidences of a numerator count once. -/
theorem criticalState_listed_numerator_occupation {W₀ : ℝ} (hW₀ : 0<W₀)
    (ht : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (T : ℝ) (k L : ℕ) (A E : Set ℝ) (N : Finset ℕ),
      (∀ n ∈ N, 0<n) → MeasurableSet E →
      (∀ v ∈ E, ∃ j : ℕ, ⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊∈N) →
      (∫ t in A, |(∫ v, Φ v)*ordinaryPrimeComplementBand (E.indicator Φ) k L t*fractionalPrimeTest (T-t)|)
        ≤ K*L*Real.exp (-T/2)*∑ n ∈ N, (1/(n:ℝ)) := by
  obtain ⟨K,hK,h⟩ := criticalState_ordinaryBand_occupation hW₀ ht hF hc he
  refine ⟨K,hK,fun T k L A E N hN hE hhit => ?_⟩
  let bins := fun n : ℕ => Ico (Real.log n) (Real.log ((n:ℝ)+1))
  let W := ⋃ n ∈ N, bins n
  have hW : MeasurableSet W := MeasurableSet.biUnion N.countable_toSet fun _ _ => measurableSet_Ico
  have htop (z : ℝ) (hz : z∈W) : z≤Real.log (((N.sup (id : ℕ → ℕ):ℕ):ℝ)+1) := by
    obtain ⟨n,hn⟩ := mem_iUnion.mp hz
    obtain ⟨hn,hz⟩ := mem_iUnion.mp hn
    have hmax : n≤N.sup id := Finset.le_sup (f := id) hn
    exact hz.2.le.trans (Real.log_le_log (by positivity) (add_le_add (Nat.cast_le.mpr hmax) le_rfl))
  have hsub : W ⊆ Icc 0 (Real.log (((N.sup (id : ℕ → ℕ):ℕ):ℝ)+1)) := by
    intro z hz
    obtain ⟨n,hn⟩ := mem_iUnion.mp hz
    obtain ⟨hc,hm⟩ := mem_iUnion.mp hn
    exact ⟨(Real.log_natCast_nonneg n).trans hm.1,htop _ hz⟩
  have hhitW : E ⊆ hitsLogNumerators T W := by
    intro v hv
    obtain ⟨j,hj⟩ := hhit v hv
    let z := digitLevel T j-v
    have hz : Real.exp z=(2:ℝ)^(j+1)*Real.exp (T-v) := by
      rw [show z=((j+1:ℕ):ℝ)*Real.log 2+(T-v) by dsimp [z,digitLevel]; ring,
        Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [← hz] at hj
    refine ⟨j,mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨hj,?_⟩⟩⟩
    exact ⟨(Real.log_le_iff_le_exp (Nat.cast_pos.mpr (hN _ hj))).mpr (Nat.floor_le (Real.exp_pos _).le),
      (Real.lt_log_iff_exp_lt (by positivity)).mpr (Nat.lt_floor_add_one _)⟩
  have hcost := h T k L A W E hW (measure_ne_top_of_subset hsub measure_Icc_lt_top.ne)
    ⟨_,htop⟩ hE hhitW
  apply hcost.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (measureReal_biUnion_finset_le (μ := volume) N bins).trans
  apply Finset.sum_le_sum
  intro n hn
  have hn₀ : 0<(n:ℝ) := Nat.cast_pos.mpr (hN n hn)
  rw [show bins n=Ico _ _ from rfl,Real.volume_real_Ico_of_le (Real.log_le_log hn₀ (by linarith))]
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0<(n:ℝ)+1) hn₀)
  rw [Real.log_div (by positivity) hn₀.ne'] at hlog
  exact hlog.trans_eq (by field_simp; ring)

private theorem band_test_integrable {Φ : ℝ → ℝ} (hi : Integrable Φ) (T : ℝ) (k L : ℕ) :
    Integrable (fun t => ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t)) := by
  let G := fun (n : ℕ) (t : ℝ) => coeff n*continuousIntegerAtom Φ n t*fractionalPrimeTest (T-t)
  let A := fun n => {t : ℝ | pastCriticalEdge n t}
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_lt
    (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const
  have hK := measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id : Measurable (fun t : ℝ => T-t))
  have hG (n : ℕ) : Integrable (G n) := by
    have h : Integrable (fun t => coeff n*continuousIntegerAtom Φ n t) :=
      ((hi.comp_sub_right _).const_mul (Real.sqrt n)⁻¹).const_mul _
    apply h.abs.mono' (h.aestronglyMeasurable.mul hK.aestronglyMeasurable)
    filter_upwards [] with t
    change ‖(coeff n*continuousIntegerAtom Φ n t)*fractionalPrimeTest (T-t)‖ ≤ |coeff n*continuousIntegerAtom Φ n t|
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (fractionalPrimeTest_bounds _).1
  apply (integrable_finsetSum (Finset.Ioc k L) (fun n _ => (hG n).indicator (hA n))).congr
  filter_upwards [] with t
  rw [ordinaryPrimeComplementBand,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : t∈A n
  · rw [indicator_of_mem h,if_pos (show pastCriticalEdge n t from h)]
  · rw [indicator_of_notMem h,if_neg (show ¬pastCriticalEdge n t from h),zero_mul]

/-- Removing every displacement which hits a listed common numerator at
any digit changes the original signed reading by at most its cardinality
times L X^(-3/2), uniformly for numerators at or above X. -/
theorem criticalState_sparse_numerator_removal {W₀ : ℝ} (hW₀ : 0<W₀)
    (ht : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (T : ℝ) (k L : ℕ) (A E : Set ℝ) (N : Finset ℕ),
      (∀ H ∈ N, Real.exp T≤H) → MeasurableSet E →
      (∀ v ∈ E, ∃ j : ℕ, ⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊∈N) →
      let m := ∫ v, Φ v
      |m*(∫ t in A, ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t)) -
       m*(∫ t in A, ordinaryPrimeComplementBand (Eᶜ.indicator Φ) k L t*fractionalPrimeTest (T-t))| ≤
        K*L*N.card*Real.exp (-3*T/2) := by
  obtain ⟨K,hK,h⟩ := criticalState_listed_numerator_occupation hW₀ ht hF hc he
  refine ⟨K,hK,fun T k L A E N hN hE hhit => ?_⟩
  let m := ∫ v, Φ v
  let f := fun (Ψ : ℝ → ℝ) (t : ℝ) => ordinaryPrimeComplementBand Ψ k L t*fractionalPrimeTest (T-t)
  have hi := ((criticalHalfLineEnergyDomain_of_groundState hF).integrable).congr he
  have hf := band_test_integrable hi T k L
  have hg := band_test_integrable (hi.indicator hE.compl) T k L
  have hpt (t : ℝ) : f Φ t-f (Eᶜ.indicator Φ) t=f (E.indicator Φ) t := by
    dsimp only [f]; rw [← sub_mul,ordinaryBand_sub_remove_displacements]
  have hchange : (∫ t in A, f Φ t)-(∫ t in A, f (Eᶜ.indicator Φ) t)=∫ t in A, f (E.indicator Φ) t := by
    rw [← integral_sub hf.integrableOn hg.integrableOn]
    exact integral_congr_ae (Eventually.of_forall hpt)
  change |m*(∫ t in A, f Φ t)-m*(∫ t in A, f (Eᶜ.indicator Φ) t)|≤_
  rw [← mul_sub,hchange,← integral_const_mul]
  have hnorm := norm_integral_le_integral_norm (μ := volume.restrict A) (fun t => m*f (E.indicator Φ) t)
  simp only [Real.norm_eq_abs] at hnorm
  have hcost := h T k L A E N (fun n hn => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hN n hn))) hE hhit
  have hsum := Finset.sum_le_sum (s := N) (g := fun _ => (Real.exp T)⁻¹) (fun n hn =>
    (show 1/(n:ℝ)≤(Real.exp T)⁻¹ by rw [one_div]; exact inv_anti₀ (Real.exp_pos _) (hN n hn)))
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  change (∫ t in A, |m*ordinaryPrimeComplementBand (E.indicator Φ) k L t*fractionalPrimeTest (T-t)|) ≤ _ at hcost
  simp_rw [mul_assoc m] at hcost
  apply (hnorm.trans hcost).trans
  calc _ ≤ K*L*Real.exp (-T/2)*((N.card:ℝ)*(Real.exp T)⁻¹) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
       _ = K*L*N.card*(Real.exp (-T/2)*Real.exp (-T)) := by rw [Real.exp_neg T]; ring
       _ = _ := by rw [← Real.exp_add]; congr 2; ring

#print axioms criticalState_sparse_numerator_removal

#print axioms criticalState_paired_cell_occupation
#print axioms criticalState_listed_numerator_occupation
end GaloisForLFunctions.ExclusionOfTheCriticalState
