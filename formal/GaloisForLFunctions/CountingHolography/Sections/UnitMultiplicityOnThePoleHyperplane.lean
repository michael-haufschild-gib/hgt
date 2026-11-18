import GaloisForLFunctions.CountingHolography.Sections.TheJetRadiusOfPoleBalancedSections

/-!
# Three units of multiplicity on the pole hyperplane

When two positive unit graphs balance one negative unit graph, their
square-root conductors are u, v and u+v. As v/u grows, two long lags
coalesce. Their difference tends to zero at a rate set by the zero width.
The ordinary prime products consequently have one common exponential bound.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology SquareRootThreshold SurfaceOfSpecZ RenormalizedIntersectionTheory
open Zeta23 ArithmeticOrientationGeometry ArithmeticScatteringHolography

private def shortLag (x : ℝ) : ℝ := 2*Real.log (1+Real.exp (-x))

/-- Degree of a unit triple as a function of the log ratio of its two
positive square-root conductors. -/
def unitTripleDegree (x : ℝ) : ℝ := 3*realSplineTrace 0 - 2*realSplineTrace (shortLag x) +
  2*(realSplineTrace (2*x) - realSplineTrace (2*x+shortLag x))

private theorem trace_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      |realSplineTrace t - realSplineTrace s| ≤ L*(t-s)*Real.exp (zetaZeroWidth*t) := by
  let L := ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ * ‖z‖
  refine ⟨L,tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _), fun s t hs hst => ?_⟩
  have hw := (zetaZeroWidth_le_iff_re_le zetaZeroWidth_nonneg).mp le_rfl
  have h := abs_two_re_lagStructure_sub_le_of_width temperedConfig_zetaZeroConfig
    zetaZeroWidth_nonneg hw hs hst
  rw [← orbitCorr_eq_re_lagStructure_spline,← orbitCorr_eq_re_lagStructure_spline,
    orbitCorr_splineCycle_eq,orbitCorr_splineCycle_eq,← mul_sub,abs_mul,abs_two] at h
  change 2*|realSplineTrace t - realSplineTrace s| ≤ 2*L*(t-s)*Real.exp (zetaZeroWidth*t) at h
  linarith only [h]

private theorem shortLag_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ shortLag x ∧ shortLag x ≤ 2*Real.exp (-x) ∧ shortLag x ≤ 2 := by
  have he := Real.exp_pos (-x)
  have he' := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1+Real.exp (-x) by positivity)
  unfold shortLag
  exact ⟨mul_nonneg two_pos.le (Real.log_nonneg (by linarith only [he])),
    by linarith only [hl],by linarith only [hl,he']⟩

/-- The diagonal is approached with a power saving in the ratio of the
square-root conductors, uniformly over all balanced unit triples. -/
theorem unitTripleDegree_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      |unitTripleDegree x-realSplineTrace 0| ≤ C*Real.exp ((2*zetaZeroWidth-1)*x) := by
  obtain ⟨L,hL,h⟩ := trace_lipschitz
  let a := zetaZeroWidth
  have ha : 0 ≤ a := zetaZeroWidth_nonneg
  refine ⟨8*L*Real.exp (2*a),by positivity,fun x hx => ?_⟩
  let d := shortLag x
  obtain ⟨hd,hd',hd₂⟩ := shortLag_bounds hx
  have hinc (s : ℝ) (hs : 0 ≤ s) : |realSplineTrace (s+d)-realSplineTrace s| ≤
      2*L*Real.exp (2*a)*Real.exp (-x+a*s) := by
    have h₀ := h s (s+d) hs (le_add_of_nonneg_right hd)
    rw [add_sub_cancel_left] at h₀
    have h₁ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add (le_refl s) hd₂) ha)
    calc _ ≤ L*d*Real.exp (a*(s+d)) := h₀
      _ ≤ L*(2*Real.exp (-x))*Real.exp (a*(s+2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd' hL) h₁ (Real.exp_pos _).le (by positivity)
      _ = _ := by
        rw [mul_add,Real.exp_add,Real.exp_add,mul_comm a 2]
        ring
  have hshort := hinc 0 le_rfl
  simp only [zero_add,mul_zero,add_zero] at hshort
  have hlong := hinc (2*x) (mul_nonneg two_pos.le hx)
  have he : -x+a*(2*x) = (2*a-1)*x := by ring
  rw [he] at hlong
  have hle : Real.exp (-x) ≤ Real.exp ((2*a-1)*x) := Real.exp_le_exp.mpr
    (by linarith only [mul_nonneg ha hx])
  have hboth := hshort.trans (mul_le_mul_of_nonneg_left hle (by positivity))
  have hab := abs_add_le (2*(realSplineTrace d-realSplineTrace 0))
    (2*(realSplineTrace (2*x+d)-realSplineTrace (2*x)))
  rw [abs_mul,abs_mul,abs_two] at hab
  have hid : unitTripleDegree x-realSplineTrace 0 =
      -(2*(realSplineTrace d-realSplineTrace 0)+2*(realSplineTrace (2*x+d)-realSplineTrace (2*x))) := by
    unfold unitTripleDegree d
    ring
  rw [hid,abs_neg]
  change _ ≤ 8*L*Real.exp (2*a)*Real.exp ((2*a-1)*x)
  linarith only [hab,hboth,hlong]

private theorem width_exponent_neg : 2*zetaZeroWidth-1 < 0 := by
  linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths]

theorem tendsto_unitTripleDegree : Tendsto unitTripleDegree atTop (𝓝 (realSplineTrace 0)) := by
  obtain ⟨C,_,h⟩ := unitTripleDegree_error
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg width_exponent_neg)
  have he' : Tendsto (fun x : ℝ => C*Real.exp ((2*zetaZeroWidth-1)*x)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,id_eq,mul_zero] using he.const_mul C
  have h₀ : Tendsto (fun x => unitTripleDegree x-realSplineTrace 0) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ => C*Real.exp ((2*zetaZeroWidth-1)*x)) _ he'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact h x hx
  simpa only [sub_add_cancel,zero_add] using h₀.add_const (realSplineTrace 0)

/-- The positive pole weight of one graph. -/
def rootDegree {N : ℕ} (i : Fin N) := Real.sqrt ((i : ℝ)+1)

private theorem rootDegree_pos {N : ℕ} (i : Fin N) : 0 < rootDegree i :=
  Real.sqrt_pos_of_pos (by positivity)

private theorem log_degree {N : ℕ} (i : Fin N) : Real.log ((i : ℝ)+1) = 2*Real.log (rootDegree i) := by
  rw [rootDegree,Real.log_sqrt (by positivity : 0 ≤ (i : ℝ)+1)]
  ring

/-- The unit triple is determined up to common dilation by the ratio of
its positive square-root conductors. The labels may coincide. -/
theorem integerProbe_unitTriple {N : ℕ} (i j k : Fin N)
    (h : positivePoleDegree (threeGraphDivisor i j k 1 1 1) = 0) :
    integerProbe N (threeGraphDivisor i j k 1 1 1) = unitTripleDegree (Real.log (rootDegree j/rootDegree i)) := by
  have hk : rootDegree k = rootDegree i+rootDegree j := by
    unfold positivePoleDegree at h
    rw [sum_threeGraphDivisor] at h
    change rootDegree i*(1 : ℤ)+rootDegree j*(1 : ℤ)-rootDegree k*(1 : ℤ) = 0 at h
    simp only [Int.cast_one,mul_one] at h
    linarith only [h]
  let x := Real.log (rootDegree j/rootDegree i)
  have hi := rootDegree_pos i
  have hj := rootDegree_pos j
  have hk' := rootDegree_pos k
  have hx : x = Real.log (rootDegree j)-Real.log (rootDegree i) := Real.log_div hj.ne' hi.ne'
  have hex : Real.exp (-x) = rootDegree i/rootDegree j := by
    rw [Real.exp_neg,show Real.exp x = rootDegree j/rootDegree i from Real.exp_log (div_pos hj hi),inv_div]
  have hd : shortLag x = 2*(Real.log (rootDegree k)-Real.log (rootDegree j)) := by
    rw [shortLag,hex,← Real.log_div hk'.ne' hj.ne',hk,add_div,div_self hj.ne',add_comm]
  rw [integerProbe_threeGraphDivisor]
  simp only [atomGram_eq_splineSeries,log_degree,sub_self,Int.cast_one,one_pow,one_mul,mul_one]
  change _ = unitTripleDegree x
  have hki : 2*Real.log (rootDegree k)-2*Real.log (rootDegree i) = 2*x+shortLag x := by rw [hd,hx]; ring
  have hji : 2*Real.log (rootDegree j)-2*Real.log (rootDegree i) = 2*x := by rw [hx]; ring
  have hkj : 2*Real.log (rootDegree k)-2*Real.log (rootDegree j) = shortLag x := by rw [hd]; ring
  rw [hki,hji,hkj]
  unfold unitTripleDegree realSplineTrace
  ring

private theorem balanced_neg {N : ℕ} (a : Fin N → ℤ) :
    positivePoleDegree (-a) = -positivePoleDegree a := by
  simp only [positivePoleDegree,Pi.neg_apply,Int.cast_neg,mul_neg,sum_neg_distrib]

private theorem positive_of_balanced_ne_zero {N : ℕ} {a : Fin N → ℤ}
    (ha : positivePoleDegree a = 0) (hne : a ≠ 0) : ∃ i, 0 < a i := by
  by_contra! h
  obtain ⟨k,hk⟩ : ∃ i, a i ≠ 0 := by
    by_contra! hall
    exact hne (funext hall)
  have hn := sum_neg' (s := (univ : Finset (Fin N)))
    (f := fun i => rootDegree i*(a i : ℝ))
    (fun i _ => mul_nonpos_of_nonneg_of_nonpos (rootDegree_pos i).le (by exact_mod_cast h i))
    ⟨k,mem_univ k,mul_neg_of_pos_of_neg (rootDegree_pos k) (by exact_mod_cast lt_of_le_of_ne (h k) hk)⟩
  exact hn.ne ha

private theorem single_of_mass_one {N : ℕ} {a : Fin N → ℤ} (hnz : a ≠ 0)
    (hm : ∑ i, |(a i : ℝ)| ≤ 1) :
    ∃ i : Fin N, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ a = Pi.single i ε := by
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! hall
    exact hnz (funext hall)
  have h₀ : 1 ≤ |a i| := by
    rcases le_total 0 (a i) with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos h]; omega
  have h₁ : (1:ℝ) ≤ |(a i : ℝ)| := by exact_mod_cast h₀
  rw [← sum_erase_add _ _ (mem_univ i)] at hm
  have hrest := sum_nonneg (s := univ.erase i) fun (j : Fin N) _ => abs_nonneg (a j : ℝ)
  have hai : |(a i : ℝ)| ≤ 1 := by linarith only [hm,hrest]
  have hz : |a i| ≤ 1 := by exact_mod_cast hai
  refine ⟨i,a i,?_,?_⟩
  · rcases le_total 0 (a i) with h | h
    · rw [abs_of_nonneg h] at hz; exact Or.inl (by omega)
    · rw [abs_of_nonpos h] at hz; exact Or.inr (by omega)
  · funext j
    by_cases hej : i = j
    · subst j; simp
    have hr := single_le_sum (f := fun k : Fin N => |(a k : ℝ)|)
      (fun k _ => abs_nonneg _) (mem_erase.mpr ⟨Ne.symm hej,mem_univ j⟩)
    have hz' : |(a j : ℝ)| = 0 := le_antisymm (by linarith only [hr,hm,h₁]) (abs_nonneg _)
    simpa only [Pi.single_apply,if_neg (Ne.symm hej)] using (show a j = 0 by exact_mod_cast abs_eq_zero.mp hz')

private theorem rootDegree_injective (N : ℕ) : Function.Injective (@rootDegree N) := by
  intro i j he
  have h := congrArg (fun x : ℝ => x^2) he
  change (Real.sqrt ((i : ℝ)+1))^2 = (Real.sqrt ((j : ℝ)+1))^2 at h
  rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)] at h
  apply Fin.ext
  exact_mod_cast add_right_cancel h

/-- Up to sign, every nonzero integral pole-balanced divisor of variation
at most three consists of two positive unit graphs and one negative unit graph. -/
theorem mass_three_classification {N : ℕ} {a : Fin N → ℤ} (ha : positivePoleDegree a = 0)
    (hm : ∑ i, |(a i : ℝ)| ≤ 3) (hnz : a ≠ 0) :
    ∃ i j k : Fin N, rootDegree i ≤ rootDegree j ∧
      (a = threeGraphDivisor i j k 1 1 1 ∨ -a = threeGraphDivisor i j k 1 1 1) := by
  obtain ⟨i,hi⟩ := positive_of_balanced_ne_zero ha hnz
  obtain ⟨k,hk'⟩ := positive_of_balanced_ne_zero (show positivePoleDegree (-a) = 0 by rw [balanced_neg,ha,neg_zero])
    (neg_ne_zero.mpr hnz)
  have hk : a k < 0 := neg_pos.mp hk'
  have hik : i ≠ k := fun e => (e ▸ hi).not_gt hk
  let b : Fin N → ℤ := a-Pi.single i 1+Pi.single k 1
  have hb (j : Fin N) : |(b j : ℝ)| + (if j=i then (1:ℝ) else 0) + (if j=k then (1:ℝ) else 0) =
      |(a j : ℝ)| := by
    by_cases h : j=i
    · subst j
      have h₁ : (1:ℝ) ≤ a i := by exact_mod_cast (show (1:ℤ) ≤ a i by omega)
      have he : b i = a i-1 := by simp [b,Pi.single_apply,hik]
      rw [he,if_pos rfl,if_neg hik,add_zero,Int.cast_sub,Int.cast_one,
        abs_of_nonneg (sub_nonneg.mpr h₁),abs_of_nonneg (zero_le_one.trans h₁),sub_add_cancel]
    by_cases h' : j=k
    · subst j
      have h₁ : (a k : ℝ) ≤ -1 := by exact_mod_cast (show a k ≤ -1 by omega)
      have he : b k = a k+1 := by simp [b,Pi.single_apply,h]
      rw [he,if_neg h,if_pos rfl,add_zero,Int.cast_add,Int.cast_one,
        abs_of_nonpos (by linarith only [h₁] : (a k : ℝ)+1 ≤ 0),
        abs_of_nonpos (by linarith only [h₁] : (a k : ℝ) ≤ 0)]
      ring
    simp [b,h,h']
  have hsum : (∑ j, (|(b j : ℝ)| + (if j=i then (1:ℝ) else 0) + (if j=k then (1:ℝ) else 0))) =
      ∑ j, |(a j:ℝ)| := sum_congr rfl fun j _ => hb j
  simp only [sum_add_distrib,sum_ite_eq',mem_univ,if_true] at hsum
  have haeq : a = b+Pi.single i 1-Pi.single k 1 := by unfold b; abel
  have hbn : b ≠ 0 := by
    intro hb0
    have he : a = threeGraphDivisor i i k 1 0 1 := by
      rw [haeq,hb0,threeGraphDivisor]
      simp only [zero_add,Pi.single_zero,add_zero,Pi.single_neg,sub_eq_add_neg]
    rw [he,positivePoleDegree,sum_threeGraphDivisor] at ha
    change rootDegree i*(1 : ℤ)+rootDegree i*(0 : ℤ)-rootDegree k*(1 : ℤ) = 0 at ha
    simp only [Int.cast_one,Int.cast_zero,mul_one,mul_zero,add_zero,sub_eq_zero] at ha
    exact hik (rootDegree_injective N ha)
  obtain ⟨j,ε,hε,hb'⟩ := single_of_mass_one hbn (by linarith only [hm,hsum])
  have horder (x y z : Fin N) (v : Fin N → ℤ)
      (he : v = threeGraphDivisor x y z 1 1 1) :
      ∃ u w : Fin N, rootDegree u ≤ rootDegree w ∧ v = threeGraphDivisor u w z 1 1 1 := by
    rcases le_total (rootDegree x) (rootDegree y) with h | h
    · exact ⟨x,y,h,he⟩
    · exact ⟨y,x,h,he.trans (by unfold threeGraphDivisor; rw [add_comm (Pi.single x 1) (Pi.single y 1)])⟩
  rcases hε with rfl | rfl
  · have he : a = threeGraphDivisor i j k 1 1 1 := by
      rw [haeq,hb',threeGraphDivisor,Pi.single_neg]
      abel
    obtain ⟨u,w,huw,h⟩ := horder i j k a he
    exact ⟨u,w,k,huw,Or.inl h⟩
  · have he : -a = threeGraphDivisor k j i 1 1 1 := by
      rw [haeq,hb',threeGraphDivisor]
      simp only [Pi.single_neg]
      abel
    obtain ⟨u,w,huw,h⟩ := horder k j i (-a) he
    exact ⟨u,w,i,huw,Or.inr h⟩

/-- Every balanced integral divisor of mass at most three has bounded
absolute degree, uniformly in all three conductor labels. -/
theorem mass_three_degree_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    positivePoleDegree a = 0 → (∑ i, |(a i : ℝ)|) ≤ 3 → |integerProbe N a| ≤ K := by
  obtain ⟨D,hD,hd⟩ := unitTripleDegree_error
  refine ⟨D+|realSplineTrace 0|,add_nonneg hD (abs_nonneg _),fun N a hbal hmass => ?_⟩
  by_cases hnz : a = 0
  · subst a
    simp only [integerProbe_eq_sum,Pi.zero_apply,Int.cast_zero,mul_zero,sum_const_zero,abs_zero]
    exact add_nonneg hD (abs_nonneg _)
  obtain ⟨i,j,k,hij,he⟩ := mass_three_classification hbal hmass hnz
  let x := Real.log (rootDegree j/rootDegree i)
  have hx : 0 ≤ x := Real.log_nonneg ((one_le_div (rootDegree_pos i)).mpr hij)
  have he' := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg width_exponent_neg.le hx)
  have hD' := mul_le_mul_of_nonneg_left he' hD
  have hu : |unitTripleDegree x| ≤ D+|realSplineTrace 0| := calc
    _ = |(unitTripleDegree x-realSplineTrace 0)+realSplineTrace 0| := by rw [sub_add_cancel]
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add ((hd x hx).trans (hD'.trans_eq (mul_one _))) le_rfl)
  rcases he with he | he
  · rw [he] at hbal ⊢
    rw [integerProbe_unitTriple i j k hbal]
    exact hu
  · have hneg : integerProbe N (-a) = integerProbe N a := by
      simp only [integerProbe_eq_sum,Pi.neg_apply,Int.cast_neg,mul_neg,neg_mul,neg_neg]
    have hbal' : positivePoleDegree (threeGraphDivisor i j k 1 1 1) = 0 := by
      rw [← he,balanced_neg,hbal,neg_zero]
    rw [← hneg,he,integerProbe_unitTriple i j k hbal']
    exact hu

/-- The ordinary-prime comparison on the entire pole hyperplane up to
three units of total variation holds with one common base. -/
theorem ordinaryPrimeGenerator_mass_three_bound :
    ∃ B : ℕ, 0 < B ∧ ∀ (N : ℕ) (a : Fin N → ℤ), positivePoleDegree a = 0 →
      (∑ i, |(a i : ℝ)|) ≤ 3 → ∀ᶠ m : ℕ in atTop,
        ordinaryPrimeGenerator (m • a) ≤ (B : ℚ)^(m^2) := by
  obtain ⟨C,hC,ha⟩ := poleBalanced_ordinary_error
  obtain ⟨K,_,hK⟩ := mass_three_degree_bound
  let H := 9*C+4+K
  let B := ⌈Real.exp H⌉₊
  have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos H)
  have hlog : H ≤ Real.log B := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil _)
  refine ⟨B,hB,fun N a hbal hmass => ?_⟩
  have hform := (abs_le.mp (hK N a hbal hmass)).1
  have hm := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hmass 2) hC
  have hcoeff : C*(∑ i, |(a i : ℝ)|)^2+4-integerProbe N a ≤ Real.log B := by
    unfold H at hlog
    linarith only [hlog,hm,hform]
  filter_upwards [ha N a hbal] with m hlim
  have hb := generator_le_power_iff (m • a) hB 1 m
  simp only [one_mul,Nat.cast_one,one_pow,mul_one] at hb
  apply hb.mpr
  linarith only [(abs_le.mp hlim).2,mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (m : ℝ))]

/-- Both orientations of a pair of balanced unit triples together have
bounded logarithmic prime product. The individual degrees can be unbounded. -/
theorem paired_mass_three_prime_products : ∃ H : ℝ, 0 ≤ H ∧ ∀ (N : ℕ) (a b : Fin N → ℤ),
    positivePoleDegree a = 0 → positivePoleDegree b = 0 →
    (∑ i, |(a i : ℝ)|) ≤ 3 → (∑ i, |(b i : ℝ)|) ≤ 3 →
    ∀ᶠ m : ℕ in atTop,
      |Real.log (ordinaryPrimeGenerator (m • (a+b)) : ℝ)+
        Real.log (ordinaryPrimeGenerator (m • (a-b)) : ℝ)| ≤ H*(m:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := poleBalanced_ordinary_error
  obtain ⟨K,hK,hq⟩ := mass_three_degree_bound
  let E := 36*C+4
  have hE : 0 ≤ E := by unfold E; positivity
  refine ⟨2*E+4*K,by positivity,fun N a b ha hb hma hmb => ?_⟩
  have hbal : positivePoleDegree (a+b) = 0 ∧ positivePoleDegree (a-b) = 0 := by
    unfold positivePoleDegree at ha hb ⊢
    simp only [Pi.add_apply,Pi.sub_apply,Int.cast_add,Int.cast_sub,mul_add,mul_sub,
      sum_add_distrib,sum_sub_distrib,ha,hb,zero_add,sub_zero,and_self]
  have hmplus : (∑ i, |((a+b) i : ℝ)|) ≤ 6 := by
    simp only [Pi.add_apply,Int.cast_add]
    have hh := sum_le_sum (s := univ) fun (i : Fin N) _ => abs_add_le (a i:ℝ) (b i:ℝ)
    rw [sum_add_distrib] at hh
    linarith only [hh,hma,hmb]
  have hmminus : (∑ i, |((a-b) i : ℝ)|) ≤ 6 := by
    simp only [Pi.sub_apply,Int.cast_sub]
    have hh := sum_le_sum (s := univ) fun (i : Fin N) _ => abs_sub (a i:ℝ) (b i:ℝ)
    rw [sum_add_distrib] at hh
    linarith only [hh,hma,hmb]
  have hsmall (v : Fin N → ℤ) (hv : (∑ i, |(v i:ℝ)|) ≤ 6) :
      C*(∑ i, |(v i:ℝ)|)^2+4 ≤ E := by
    unfold E
    linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hv 2) hC]
  have hforms : |integerProbe N (a+b)+integerProbe N (a-b)| ≤ 4*K := by
    rw [integerProbe_parallelogram]
    have hab := abs_add_le (2*integerProbe N a) (2*integerProbe N b)
    rw [abs_mul,abs_mul,abs_two] at hab
    linarith only [hab,hq N a ha hma,hq N b hb hmb]
  filter_upwards [h N _ hbal.1,h N _ hbal.2] with m h₁ h₂
  have ht : 0 ≤ (m:ℝ)^2 := sq_nonneg _
  obtain ⟨hp,hp'⟩ := abs_le.mp (h₁.trans (mul_le_mul_of_nonneg_right (hsmall _ hmplus) ht))
  obtain ⟨hm,hm'⟩ := abs_le.mp (h₂.trans (mul_le_mul_of_nonneg_right (hsmall _ hmminus) ht))
  obtain ⟨hqlo,hqhi⟩ := abs_le.mp hforms
  rw [abs_le]
  constructor <;> linarith only [hp,hp',hm,hm',mul_le_mul_of_nonneg_right hqlo ht,
    mul_le_mul_of_nonneg_right hqhi ht]

#print axioms paired_mass_three_prime_products
#print axioms tendsto_unitTripleDegree
#print axioms mass_three_classification
#print axioms ordinaryPrimeGenerator_mass_three_bound

end GaloisForLFunctions.CountingHolography.Sections
