import GaloisForLFunctions.RHTower.ChiPrimeGaussianHyperbolicCore
import GaloisForLFunctions.RHTower.PrimeShortIntervalsFiveEighths

/-!
# Unbounded signed variation of the actual Gaussian prime cubic

The source near-prime-pair family and the every-window prime theorem populate
disjoint positive and negative phase sectors. Every constructed triple lies in
the literal full band and in the physical window plateau. The actual Gaussian
amplitude and both complete kernel errors preserve each sign. Consequently
both real Jordan parts of the complete noncontracting physical cubic tend to
infinity after contraction-scale normalization. This does not evaluate their
difference; the complete signed asymptotic remains open.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower PrimeCells

/-- Actual central prime pairs, independent of any selected gap construction. -/
def primeGaussianCentralPair (N : ℝ) (r p : ℕ) : Prop :=
  r.Prime ∧ p.Prime ∧ 3*N/2 < r ∧ (r:ℝ) ≤ 25*N/16 ∧
    3*N/2 < p ∧ (p:ℝ) ≤ 25*N/16

private def sectorN (m : ℕ) : ℝ := primeGaussianHyperbolicConductor m

private theorem nearPairs_central {m r p : ℕ} (h : (r,p) ∈ primeGaussianNearPairs m) :
    primeGaussianCentralPair (sectorN m) r p := by
  obtain ⟨hr,hp,hrl,hru,hpl,hpu,_,_⟩ := primeGaussianNearPairs_mem h
  exact ⟨hr,hp,hrl,hru,hpl,hpu⟩

private def sectorH (m : ℕ) : ℝ := primeGaussianNearWidth m

private theorem sectorH_pos (m : ℕ) : 0 < sectorH m := by
  dsimp only [sectorH]
  exact_mod_cast primeGaussianNearWidth_pos m

private theorem sector_four (m : ℕ) : sectorH m ^ 4 = sectorN m := by
  dsimp only [sectorH,sectorN]
  exact_mod_cast primeGaussianNearWidth_pow_four m

private theorem sectorN_pos (m : ℕ) : 0 < sectorN m := by
  rw [← sector_four]
  exact pow_pos (sectorH_pos m) 4

private theorem sectorN_tendsto : Tendsto sectorN atTop atTop :=
  tendsto_primeGaussianHyperbolicConductor

private theorem sectorH_tendsto : Tendsto sectorH atTop atTop :=
  tendsto_primeGaussianNearWidth

private theorem eventually_sector_window_scale :
    ∀ᶠ m : ℕ in atTop,
      2*(2*sectorN m)^((2:ℝ)/3) ≤ sectorN m/(12*sectorH m) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp sectorH_tendsto
  filter_upwards [ht.eventually_ge_atTop 48] with m hm
  change 48 ≤ sectorH m^((1:ℝ)/3) at hm
  have hh := sectorH_pos m
  have hN := sectorN_pos m
  have htwo : (2:ℝ)^((2:ℝ)/3) ≤ 2 := by
    calc
      _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  have he : (2*sectorN m)^((2:ℝ)/3) =
      (2:ℝ)^((2:ℝ)/3)*sectorH m^((8:ℝ)/3) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le, ← sector_four,
      ← Real.rpow_natCast_mul hh.le]
    norm_num
  have hp : sectorH m^((8:ℝ)/3)*sectorH m^((1:ℝ)/3) = sectorH m^3 := by
    rw [← Real.rpow_add hh]
    norm_num
  have hb := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hh.le ((8:ℝ)/3))
  rw [hp] at hb
  have heN : sectorN m/(12*sectorH m) = sectorH m^3/12 := by
    rw [← sector_four]
    field_simp
  rw [he,heN]
  have he2 := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hh.le ((8:ℝ)/3))
  linarith

private theorem exists_sector_prime_window_lower :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ N a L : ℝ, X ≤ N → N ≤ a → a+L ≤ 2*N →
      2*(2*N)^((2:ℝ)/3) ≤ L →
      L/(8*Real.log N) ≤ (windowPrimes a (a+L)).card := by
  obtain ⟨X,hX,hθ⟩ := exists_theta_window_lower_five_eighths
    (α := (2:ℝ)/3) (by norm_num) (by norm_num)
  refine ⟨max X 2,le_max_right _ _,?_⟩
  intro N a L hN hNa htop hL
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  have ha0 : 0 < a := by linarith
  have hL0 : 0 ≤ L := (by positivity : 0 ≤ 2*(2*N)^((2:ℝ)/3)).trans hL
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have haX : X ≤ a := (le_max_left _ _).trans (hN.trans hNa)
  have hb := hθ a L haX hL0
  have hpow : (a+L)^((2:ℝ)/3) ≤ (2*N)^((2:ℝ)/3) :=
    Real.rpow_le_rpow (by linarith) htop (by norm_num)
  have hc := theta_sub_le_card_mul_log ha0.le (by linarith : a ≤ a+L)
  have hlogtop : Real.log (a+L) ≤ 2*Real.log N := by
    calc
      _ ≤ Real.log (2*N) := Real.log_le_log (by linarith) htop
      _ = Real.log 2 + Real.log N := Real.log_mul (by norm_num) hN0.ne'
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0:ℝ) < 2) hN2]
  have hmul := mul_le_mul_of_nonneg_left hlogtop
    (Nat.cast_nonneg (α:=ℝ) (windowPrimes a (a+L)).card)
  apply (div_le_iff₀ (by positivity : 0 < 8*Real.log N)).mpr
  nlinarith

private def sectorWindow (r : ℕ) (d β : ℝ) (k : ℕ) : Finset ℕ :=
  windowPrimes ((r:ℝ)+(r:ℝ)/d*((k:ℝ)+β))
    ((r:ℝ)+(r:ℝ)/d*((k:ℝ)+β+1/12))

private def sectorPrimes (r : ℕ) (d β : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊d/128⌋₊).biUnion (sectorWindow r d β)

private theorem sector_window_geometry {N d β : ℝ} {r k : ℕ}
    (hN : 0 < N) (hrl : N ≤ (r:ℝ)) (hru : (r:ℝ) ≤ 2*N)
    (hd : 256 ≤ d) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1/2)
    (hk : k ∈ Finset.Icc 1 ⌊d/128⌋₊) :
    N ≤ (r:ℝ)+(r:ℝ)/d*((k:ℝ)+β) ∧
    (r:ℝ)+(r:ℝ)/d*((k:ℝ)+β+1/12) ≤ (r:ℝ)+N/32 := by
  have hd0 : 0 < d := by linarith
  have hr0 : (0:ℝ) < r := hN.trans_le hrl
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hku : (k:ℝ) ≤ d/128 :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans (Nat.floor_le (by linarith))
  constructor
  · have hh : 0 ≤ (r:ℝ)/d*((k:ℝ)+β) := by positivity
    linarith
  · have hx : (k:ℝ)+β+1/12 ≤ d/64 := by linarith
    have hprod := mul_le_mul_of_nonneg_left hx (div_nonneg hr0.le hd0.le)
    have he : (r:ℝ)/d*(d/64) = (r:ℝ)/64 := by field_simp
    rw [he] at hprod
    linarith

private theorem mem_sectorWindow {N d β : ℝ} {r k q : ℕ}
    (hN : 0 < N) (hrl : N ≤ (r:ℝ)) (hru : (r:ℝ) ≤ 2*N)
    (hd : 256 ≤ d) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1/2)
    (hk : k ∈ Finset.Icc 1 ⌊d/128⌋₊) (hq : q ∈ sectorWindow r d β k) :
    q.Prime ∧ (r:ℝ) < q ∧ (q:ℝ) ≤ (r:ℝ)+N/32 ∧
    (k:ℝ)+β < d*((q:ℝ)-r)/r ∧ d*((q:ℝ)-r)/r ≤ (k:ℝ)+β+1/12 := by
  have hr0 : (0:ℝ) < r := hN.trans_le hrl
  have hd0 : 0 < d := by linarith
  obtain ⟨ha,hb⟩ := sector_window_geometry hN hrl hru hd hβ0 hβ1 hk
  obtain ⟨hqp,hql,hqu⟩ := (mem_windowPrimes (hN.le.trans ha)
    (by positivity : 0 ≤ (r:ℝ)+(r:ℝ)/d*((k:ℝ)+β+1/12))).mp hq
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hpart : 0 ≤ (r:ℝ)/d*((k:ℝ)+β) := by positivity
  refine ⟨hqp,by linarith,hqu.trans hb,?_,?_⟩
  · apply (lt_div_iff₀ hr0).mpr
    have hh := mul_lt_mul_of_pos_right hql hd0
    have he : ((r:ℝ)+(r:ℝ)/d*((k:ℝ)+β))*d =
        (r:ℝ)*d+(r:ℝ)*((k:ℝ)+β) := by field_simp
    rw [he] at hh
    nlinarith only [hh]
  · apply (div_le_iff₀ hr0).mpr
    have hh := mul_le_mul_of_nonneg_right hqu hd0.le
    have he : ((r:ℝ)+(r:ℝ)/d*((k:ℝ)+β+1/12))*d =
        (r:ℝ)*d+(r:ℝ)*((k:ℝ)+β+1/12) := by field_simp
    rw [he] at hh
    nlinarith only [hh]

private theorem sectorWindows_disjoint {N d β : ℝ} {r : ℕ}
    (hN : 0 < N) (hrl : N ≤ (r:ℝ)) (hru : (r:ℝ) ≤ 2*N)
    (hd : 256 ≤ d) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1/2) :
    (↑(Finset.Icc 1 ⌊d/128⌋₊):Set ℕ).PairwiseDisjoint (sectorWindow r d β) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro q hqi hqj
  have hiq := mem_sectorWindow hN hrl hru hd hβ0 hβ1 hi hqi
  have hjq := mem_sectorWindow hN hrl hru hd hβ0 hβ1 hj hqj
  rcases lt_or_gt_of_ne hij with hij|hji
  · have hijR : (i:ℝ)+1 ≤ j := by exact_mod_cast hij
    linarith [hiq.2.2.2.2,hjq.2.2.2.1]
  · have hjiR : (j:ℝ)+1 ≤ i := by exact_mod_cast hji
    linarith [hjq.2.2.2.2,hiq.2.2.2.1]

private theorem eventually_sectorPrimes_count :
    ∀ᶠ m : ℕ in atTop, ∀ r : ℕ, ∀ d β : ℝ,
      sectorN m ≤ r → (r:ℝ) ≤ 25*sectorN m/16 →
      256 ≤ d → d ≤ sectorH m → 0 ≤ β → β ≤ 1/2 →
      sectorN m/(24576*Real.log (sectorN m)) ≤ (sectorPrimes r d β).card := by
  obtain ⟨X,hX,hcount⟩ := exists_sector_prime_window_lower
  filter_upwards [sectorN_tendsto.eventually_ge_atTop X,eventually_sector_window_scale]
    with m hmX hscale
  intro r d β hrl hru hd hdh hβ0 hβ1
  have hN2 : 2 ≤ sectorN m := hX.trans hmX
  have hN0 := sectorN_pos m
  have hh0 := sectorH_pos m
  have hlog : 0 < Real.log (sectorN m) := Real.log_pos (by linarith)
  have hr0 : (0:ℝ) < r := hN0.trans_le hrl
  have hd0 : 0 < d := by linarith
  have hru2 : (r:ℝ) ≤ 2*sectorN m := by linarith
  have hrow (k : ℕ) (hk : k ∈ Finset.Icc 1 ⌊d/128⌋₊) :
      sectorN m/(96*d*Real.log (sectorN m)) ≤ (sectorWindow r d β k).card := by
    let a := (r:ℝ)+(r:ℝ)/d*((k:ℝ)+β)
    let L := (r:ℝ)/(12*d)
    obtain ⟨ha,hb⟩ := sector_window_geometry hN0 hrl hru2 hd hβ0 hβ1 hk
    have he : a+L = (r:ℝ)+(r:ℝ)/d*((k:ℝ)+β+1/12) := by dsimp [a,L]; ring
    have hab : a+L ≤ 2*sectorN m := by rw [he]; linarith
    have hL : sectorN m/(12*sectorH m) ≤ L := by
      dsimp [L]
      exact (div_le_div_of_nonneg_left hN0.le (by positivity) (by nlinarith)).trans
        (div_le_div_of_nonneg_right hrl (by positivity))
    have hc := hcount (sectorN m) a L hmX ha hab (hscale.trans hL)
    rw [he] at hc
    change L/(8*Real.log (sectorN m)) ≤ ((sectorWindow r d β k).card:ℝ) at hc
    apply le_trans ?_ hc
    dsimp [L]
    calc
      _ = (sectorN m/(12*d))/(8*Real.log (sectorN m)) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hrl (by positivity)) (by positivity)
  have hkcard : d/256 ≤ ((Finset.Icc 1 ⌊d/128⌋₊).card:ℝ) := by
    rw [Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    have hh := Nat.lt_floor_add_one (d/128)
    linarith
  rw [sectorPrimes,Finset.card_biUnion (sectorWindows_disjoint hN0 hrl hru2 hd hβ0 hβ1),Nat.cast_sum]
  calc
    _ = (d/256)*(sectorN m/(96*d*Real.log (sectorN m))) := by field_simp; ring
    _ ≤ ((Finset.Icc 1 ⌊d/128⌋₊).card:ℝ)*(sectorN m/(96*d*Real.log (sectorN m))) :=
      mul_le_mul_of_nonneg_right hkcard (by positivity)
    _ = ∑ _k ∈ Finset.Icc 1 ⌊d/128⌋₊, sectorN m/(96*d*Real.log (sectorN m)) := by simp
    _ ≤ _ := Finset.sum_le_sum hrow

private def sectorSign (b : Bool) : ℝ := if b then -1 else 1
private def sectorShift (b : Bool) : ℝ := if b then 1/2 else 0
private theorem sectorSign_abs (b : Bool) : |sectorSign b| = 1 := by cases b <;> norm_num [sectorSign]
private theorem sectorShift_bounds (b : Bool) : 0 ≤ sectorShift b ∧ sectorShift b ≤ 1/2 := by
  cases b <;> norm_num [sectorShift]

private theorem osc_re_cos (x : ℝ) : (bourgainOscillation x).re = Real.cos x := by
  simp only [bourgainOscillation,Complex.exp_re,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,one_mul,mul_zero,sub_zero,zero_add,Real.exp_zero]

private theorem osc_re_neg (x : ℝ) : (bourgainOscillation (-x)).re = (bourgainOscillation x).re := by
  rw [osc_re_cos,osc_re_cos,Real.cos_neg]

private theorem sector_center_re (b : Bool) (k : ℕ) :
    (bourgainOscillation (2*Real.pi*((k:ℝ)+sectorShift b))).re = sectorSign b := by
  rw [osc_re_cos]
  cases b
  · simp only [sectorShift,sectorSign,Bool.false_eq_true,ite_false,add_zero]
    rw [show 2*Real.pi*(k:ℝ) = (k:ℝ)*(2*Real.pi) by ring,Real.cos_nat_mul_two_pi]
  · simp only [sectorShift,sectorSign,ite_true]
    rw [show 2*Real.pi*((k:ℝ)+1/2) = (k:ℝ)*(2*Real.pi)+Real.pi by ring,
      Real.cos_nat_mul_two_pi_add_pi]

private theorem sector_phase_sign (b : Bool) (k : ℕ) {x : ℝ}
    (hxl : (k:ℝ)+sectorShift b < x) (hxu : x ≤ (k:ℝ)+sectorShift b+1/12) :
    1/3 ≤ sectorSign b*(bourgainOscillation (2*Real.pi*x)).re := by
  have hdelta0 : 0 ≤ 2*Real.pi*(x-((k:ℝ)+sectorShift b)) :=
    mul_nonneg (by positivity) (by linarith)
  have hdelta := mul_le_mul_of_nonneg_left (show x-((k:ℝ)+sectorShift b) ≤ 1/12 by linarith)
    (by positivity : 0 ≤ 2*Real.pi)
  have habs : |2*Real.pi*x-2*Real.pi*((k:ℝ)+sectorShift b)| ≤ 2/3 := by
    rw [show 2*Real.pi*x-2*Real.pi*((k:ℝ)+sectorShift b) =
      2*Real.pi*(x-((k:ℝ)+sectorShift b)) by ring,abs_of_nonneg hdelta0]
    nlinarith [Real.pi_lt_four]
  have hn := (norm_bourgainOscillation_sub_le (2*Real.pi*x)
    (2*Real.pi*((k:ℝ)+sectorShift b))).trans habs
  have hr := (Complex.abs_re_le_norm _).trans hn
  simp only [Complex.sub_re,sector_center_re] at hr
  rw [abs_le] at hr
  cases b <;> norm_num only [sectorSign,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul] at * <;>
    linarith

private theorem sector_full_geometry {m r p q : ℕ} {b : Bool}
    (hrp : primeGaussianCentralPair (sectorN m) r p) (hd : 256 ≤ |(p:ℝ)-r|)
    (hq : q ∈ sectorPrimes r |(p:ℝ)-r| (sectorShift b)) :
    r.Prime ∧ p.Prime ∧ q.Prime ∧
    sectorN m < r ∧ (r:ℝ) ≤ 2*sectorN m ∧
    sectorN m < p ∧ (p:ℝ) ≤ 2*sectorN m ∧
    sectorN m < q ∧ (q:ℝ) ≤ 2*sectorN m ∧ p ≠ r ∧ q ≠ r ∧
    (r:ℝ) < q ∧ (q:ℝ) ≤ (r:ℝ)+sectorN m/32 := by
  have hcentral := hrp
  obtain ⟨hrP,hpP,hrl,hru,hpl,hpu⟩ := hcentral
  have hN := sectorN_pos m
  change 3*sectorN m/2 < r at hrl
  change (r:ℝ) ≤ 25*sectorN m/16 at hru
  change 3*sectorN m/2 < p at hpl
  change (p:ℝ) ≤ 25*sectorN m/16 at hpu
  obtain ⟨k,hk,hq⟩ := Finset.mem_biUnion.mp hq
  have hqs := mem_sectorWindow hN (by linarith) (by linarith) hd
    (sectorShift_bounds b).1 (sectorShift_bounds b).2 hk hq
  refine ⟨hrP,hpP,hqs.1,by linarith,by linarith,by linarith,by linarith,
    by linarith [hqs.2.1],by linarith [hqs.2.2.1],?_,?_,hqs.2.1,hqs.2.2.1⟩
  · intro he
    subst p
    simp only [sub_self,abs_zero] at hd
    linarith
  · intro he
    subst q
    exact (lt_irrefl _) hqs.2.1

private theorem sector_cubic_phase_sign {m r p q : ℕ} (b : Bool)
    (hrp : primeGaussianCentralPair (sectorN m) r p) (hd : 256 ≤ |(p:ℝ)-r|)
    (hq : q ∈ sectorPrimes r |(p:ℝ)-r| (sectorShift b)) :
    1/3 ≤ sectorSign b*(bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))).re := by
  have hcentral := hrp
  obtain ⟨hrP,hpP,hrl,hru,hpl,hpu⟩ := hcentral
  have hN := sectorN_pos m
  change 3*sectorN m/2 < r at hrl
  change (r:ℝ) ≤ 25*sectorN m/16 at hru
  obtain ⟨k,hk,hq⟩ := Finset.mem_biUnion.mp hq
  have hqs := mem_sectorWindow hN (by linarith) (by linarith) hd
    (sectorShift_bounds b).1 (sectorShift_bounds b).2 hk hq
  have hh := sector_phase_sign b k hqs.2.2.2.1 hqs.2.2.2.2
  rw [primeGaussianCubic_phase_recenter p q hrP.pos]
  by_cases hpr : 0 ≤ (p:ℝ)-r
  · simpa only [abs_of_nonneg hpr] using hh
  · rw [abs_of_neg (lt_of_not_ge hpr)] at hh
    have he : 2*Real.pi*((-((p:ℝ)-r))*((q:ℝ)-r)/r) =
        -(2*Real.pi*(((p:ℝ)-r)*((q:ℝ)-r)/r)) := by ring
    rw [he,osc_re_neg] at hh
    exact hh

private theorem sector_cubic_window {m r p q : ℕ} {b : Bool}
    (hrp : primeGaussianCentralPair (sectorN m) r p) (hd : 256 ≤ |(p:ℝ)-r|)
    (hq : q ∈ sectorPrimes r |(p:ℝ)-r| (sectorShift b)) :
    bagPhysicalHeightWindow ((p:ℝ)*q/((r:ℝ)*sectorN m)) = 1 := by
  have hcentral := hrp
  obtain ⟨_,_,hrl,hru,hpl,hpu⟩ := hcentral
  have hN := sectorN_pos m
  change 3*sectorN m/2 < r at hrl
  change (r:ℝ) ≤ 25*sectorN m/16 at hru
  change 3*sectorN m/2 < p at hpl
  change (p:ℝ) ≤ 25*sectorN m/16 at hpu
  obtain ⟨_,_,_,_,_,_,_,hNq,_,_,_,hqr,hqrU⟩ := sector_full_geometry hrp hd hq
  have hr0 : (0:ℝ) < r := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have hq0 : (0:ℝ) < q := hN.trans hNq
  have hlo := mul_le_mul_of_nonneg_left hqr.le hp0.le
  have hhi := mul_le_mul hpu hqrU hq0.le (by positivity : 0 ≤ 25*sectorN m/16)
  have hpr := mul_lt_mul_of_pos_right hpl hr0
  have hrN := mul_lt_mul_of_pos_right hrl hN
  have hl : (5:ℝ)/4 ≤ (p:ℝ)*q/((r:ℝ)*sectorN m) := by
    apply (le_div_iff₀ (mul_pos hr0 hN)).mpr
    nlinarith [mul_pos hr0 hN]
  have hu : (p:ℝ)*q/((r:ℝ)*sectorN m) ≤ (7:ℝ)/4 := by
    apply (div_le_iff₀ (mul_pos hr0 hN)).mpr
    nlinarith [sq_nonneg (sectorN m)]
  apply bagPhysicalHeightWindow.one_of_mem_closedBall
  change dist ((p:ℝ)*q/((r:ℝ)*sectorN m)) (3/2) ≤ 1/4
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith

private def sectorCutoffFloor : ℝ := (smoothAFECutoff 2).re
private theorem sectorCutoffFloor_pos : 0 < sectorCutoffFloor :=
  smoothAFECutoff_re_pos (by norm_num)

private theorem sector_cutoff {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) :
    smoothAFECutoff x = ((smoothAFECutoff x).re:ℂ) ∧
      sectorCutoffFloor ≤ (smoothAFECutoff x).re := by
  constructor
  · apply Complex.ext <;> simp [smoothAFECutoff_im_eq_zero hx]
  · exact smoothAFECutoff_re_antitoneOn hx (by norm_num) hx2

private theorem sector_main_signed {m r p q : ℕ} (b : Bool)
    (hrp : primeGaussianCentralPair (sectorN m) r p) (hd : 256 ≤ |(p:ℝ)-r|)
    (hq : q ∈ sectorPrimes r |(p:ℝ)-r| (sectorShift b)) :
    sectorCutoffFloor^3/(3*sectorN m) ≤
      sectorSign b*(primeGaussianCubicMainEntry (sectorN m) p q r).re := by
  obtain ⟨_,_,_,hNr,hrN,hNp,hpN,hNq,hqN,_,_,_,_⟩ := sector_full_geometry hrp hd hq
  have hN := sectorN_pos m
  have hv := sectorCutoffFloor_pos
  have hr0 : (0:ℝ) < r := hN.trans hNr
  obtain ⟨hpr,hpv⟩ := sector_cutoff (div_pos (hN.trans hNp) hN) ((div_le_iff₀ hN).mpr hpN)
  obtain ⟨hqr,hqv⟩ := sector_cutoff (div_pos (hN.trans hNq) hN) ((div_le_iff₀ hN).mpr hqN)
  obtain ⟨hrr,hrv⟩ := sector_cutoff (div_pos hr0 hN) ((div_le_iff₀ hN).mpr hrN)
  have hW := sector_cubic_window hrp hd hq
  have hphase := sector_cubic_phase_sign b hrp hd hq
  let a := (smoothAFECutoff ((p:ℝ)/sectorN m)).re
  let c := (smoothAFECutoff ((q:ℝ)/sectorN m)).re
  let e := (smoothAFECutoff ((r:ℝ)/sectorN m)).re
  have ha : 0 ≤ a := hv.le.trans hpv
  have hc : 0 ≤ c := hv.le.trans hqv
  have he : 0 ≤ e := hv.le.trans hrv
  have hace : sectorCutoffFloor^3 ≤ a*c*e := by
    have hac := mul_le_mul hpv hqv hv.le ha
    have hh := mul_le_mul hac hrv hv.le (mul_nonneg ha hc)
    simpa only [pow_succ,pow_zero,one_mul] using hh
  have hf : 1/sectorN m ≤ 2*Real.pi/r := by
    apply (div_le_div_iff₀ hN hr0).mpr
    nlinarith [Real.pi_gt_three]
  have hamp : sectorCutoffFloor^3/sectorN m ≤ 2*Real.pi/r*(a*c*e) := by
    simpa only [one_mul,div_mul_eq_mul_div] using
      mul_le_mul hf hace (by positivity : 0 ≤ sectorCutoffFloor^3) (by positivity : 0 ≤ 2*Real.pi/r)
  have heq : (primeGaussianCubicMainEntry (sectorN m) p q r).re =
      (2*Real.pi/r*(a*c*e))*(bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))).re := by
    unfold primeGaussianCubicMainEntry
    rw [hpr,hqr,hrr,hW]
    simp only [Complex.conj_ofReal,Complex.ofReal_one,mul_one]
    have hfac : (2*Real.pi:ℂ)*(a:ℂ)*(c:ℂ)*(e:ℂ)/(r:ℂ) =
        ((2*Real.pi/r*(a*c*e):ℝ):ℂ) := by push_cast; ring
    change ((2*Real.pi:ℂ)*(a:ℂ)*(c:ℂ)*(e:ℂ)/(r:ℂ)*
      bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))).re = _
    rw [hfac]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [heq]
  calc
    _ = (sectorCutoffFloor^3/sectorN m)*(1/3) := by ring
    _ ≤ (2*Real.pi/r*(a*c*e))*(sectorSign b*
        (bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))).re) :=
      mul_le_mul hamp hphase (by norm_num)
        (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg ha hc) he))
    _ = _ := by ring

private theorem sector_primeProfileBand {N : ℝ} {p : ℕ} (hN : 0 < N)
    (hp : p.Prime) (hNp : N < p) (hpN : (p:ℝ) ≤ 2*N) : p ∈ primeProfileBand N := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
    ⟨(Nat.floor_lt hN.le).mpr hNp,Nat.le_floor hpN⟩,hp⟩

private theorem eventually_sector_gap :
    ∀ᶠ m : ℕ in atTop, ∀ r p : ℕ, (r,p) ∈ primeGaussianNearPairs m → 256 ≤ |(p:ℝ)-r| := by
  filter_upwards [sectorH_tendsto.eventually_ge_atTop (256*10000000)] with m hm
  intro r p hp
  obtain ⟨_,_,_,_,_,_,hd,_⟩ := primeGaussianNearPairs_mem hp
  change sectorH m/10000000 < |(p:ℝ)-r| at hd
  linarith

private def sectorPhysicalEntry (N : ℝ) (r p q : ℕ) : ℂ :=
  primeGaussianCubicCoefficient N p q r * primeGaussianCubicKernel N p q r

private theorem eventually_sector_physical_signed :
    ∀ᶠ m : ℕ in atTop, ∀ b : Bool, ∀ r p q : ℕ,
      primeGaussianCentralPair (sectorN m) r p → 256 ≤ |(p:ℝ)-r| →
      q ∈ sectorPrimes r |(p:ℝ)-r| (sectorShift b) →
      sectorCutoffFloor^3/(6*sectorN m) ≤ sectorSign b*(sectorPhysicalEntry (sectorN m) r p q).re := by
  obtain ⟨C,hC,herror⟩ := exists_primeGaussianCubic_entry_error
  have hv := sectorCutoffFloor_pos
  filter_upwards [sectorN_tendsto.eventually_gt_atTop 1,
    sectorN_tendsto.eventually_ge_atTop (6*C/sectorCutoffFloor^3)] with m hN1 hscale
  intro b r p q hrp hd hq
  obtain ⟨hrP,hpP,hqP,hNr,hrN,hNp,hpN,hNq,hqN,_,_,_,_⟩ := sector_full_geometry hrp hd hq
  have hN := sectorN_pos m
  have hmain := sector_main_signed b hrp hd hq
  have herr := herror _ hN1 p (sector_primeProfileBand hN hpP hNp hpN)
    q (sector_primeProfileBand hN hqP hNq hqN) r (sector_primeProfileBand hN hrP hNr hrN)
  have hreal : |sectorSign b*((sectorPhysicalEntry (sectorN m) r p q).re-
      (primeGaussianCubicMainEntry (sectorN m) p q r).re)| ≤ C/(sectorN m)^2 := by
    rw [abs_mul,sectorSign_abs,one_mul]
    have hres := Complex.abs_re_le_norm (sectorPhysicalEntry (sectorN m) r p q-
      primeGaussianCubicMainEntry (sectorN m) p q r)
    simpa only [Complex.sub_re] using hres.trans herr
  have hsmall : C/(sectorN m)^2 ≤ sectorCutoffFloor^3/(6*sectorN m) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := (div_le_iff₀ (pow_pos hv 3)).mp hscale
    nlinarith only [mul_le_mul_of_nonneg_right hh hN.le]
  rw [abs_le] at hreal
  have heq : sectorCutoffFloor^3/(3*sectorN m) = 2*(sectorCutoffFloor^3/(6*sectorN m)) := by ring
  linarith [hreal.1]

/-- Literal positive or negative physical q-variation for one ordered pair. -/
def primeGaussianCubicSignedRow (b : Bool) (N : ℝ) (rp : ℕ × ℕ) : ℝ :=
  ∑ q ∈ primeProfileBand N,
    if rp.2 = rp.1 ∨ q = rp.1 then 0 else max (sectorSign b*(sectorPhysicalEntry N rp.1 rp.2 q).re) 0

/-- Positive (`false`) or negative (`true`) real variation of the entire actual physical
noncontracting Gaussian prime cubic. Every full-band triple is retained. -/
def primeGaussianCubicSignedVariation (negative : Bool) (N : ℝ) : ℝ :=
  ∑ rp ∈ primeProfileBand N ×ˢ primeProfileBand N, primeGaussianCubicSignedRow negative N rp

private theorem sectorJordanRow_nonneg (b : Bool) (N : ℝ) (rp : ℕ × ℕ) :
    0 ≤ primeGaussianCubicSignedRow b N rp := by
  apply Finset.sum_nonneg
  intro q _
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

private theorem eventually_sectorJordanRow_lower_central :
    ∀ᶠ m : ℕ in atTop, ∀ b : Bool, ∀ r p : ℕ,
      primeGaussianCentralPair (sectorN m) r p →
      256 ≤ |(p:ℝ)-r| → |(p:ℝ)-r| ≤ sectorH m →
      (sectorCutoffFloor^3/147456)/Real.log (sectorN m) ≤ primeGaussianCubicSignedRow b (sectorN m) (r,p) := by
  have hv := sectorCutoffFloor_pos
  filter_upwards [eventually_sectorPrimes_count,eventually_sector_physical_signed,
    sectorN_tendsto.eventually_gt_atTop 1] with m hcount hsign hN1
  intro b r p hrp hd hdu
  have hN := sectorN_pos m
  have hlog : 0 < Real.log (sectorN m) := Real.log_pos hN1
  have hcentral := hrp
  obtain ⟨_,_,hrl,hru,_,_⟩ := hcentral
  change 3*sectorN m/2 < r at hrl
  change (r:ℝ) ≤ 25*sectorN m/16 at hru
  have hc := hcount r |(p:ℝ)-r| (sectorShift b) (by linarith) hru hd hdu
    (sectorShift_bounds b).1 (sectorShift_bounds b).2
  let Q := sectorPrimes r |(p:ℝ)-r| (sectorShift b)
  have hsub : Q ⊆ primeProfileBand (sectorN m) := by
    intro q hq
    obtain ⟨_,_,hqP,_,_,_,_,hNq,hqN,_,_,_,_⟩ := sector_full_geometry hrp hd hq
    exact sector_primeProfileBand hN hqP hNq hqN
  calc
    _ = (sectorN m/(24576*Real.log (sectorN m)))*(sectorCutoffFloor^3/(6*sectorN m)) := by
      field_simp; ring
    _ ≤ (Q.card:ℝ)*(sectorCutoffFloor^3/(6*sectorN m)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = ∑ _q ∈ Q, sectorCutoffFloor^3/(6*sectorN m) := by simp
    _ ≤ ∑ q ∈ Q, (if p=r ∨ q=r then 0 else max (sectorSign b*(sectorPhysicalEntry (sectorN m) r p q).re) 0) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨_,_,_,_,_,_,_,_,_,hpr,hqr,_,_⟩ := sector_full_geometry hrp hd hq
      rw [if_neg (not_or.mpr ⟨hpr,hqr⟩)]
      exact (hsign b r p q hrp hd hq).trans (le_max_left _ _)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _ _
      split_ifs
      · exact le_rfl
      · exact le_max_right _ _

private theorem eventually_sectorJordanRow_lower :
    ∀ᶠ m : ℕ in atTop, ∀ b : Bool, ∀ r p : ℕ, (r,p) ∈ primeGaussianNearPairs m →
      (sectorCutoffFloor^3/147456)/Real.log (sectorN m) ≤ primeGaussianCubicSignedRow b (sectorN m) (r,p) := by
  filter_upwards [eventually_sectorJordanRow_lower_central,eventually_sector_gap] with m hm hg
  intro b r p hrp
  obtain ⟨_,_,_,_,_,_,_,hdu⟩ := primeGaussianNearPairs_mem hrp
  exact hm b r p (nearPairs_central hrp) (hg r p hrp) hdu

/-- Every central pair in the full admissible gap range supplies both signed q-variations. -/
theorem exists_primeGaussianCentralPair_signed_row :
    ∃ c:ℝ, 0<c ∧ ∀ᶠ m:ℕ in atTop, ∀ b:Bool, ∀ r p:ℕ,
      primeGaussianCentralPair (primeGaussianHyperbolicConductor m) r p →
      256 ≤ |(p:ℝ)-r| → |(p:ℝ)-r| ≤ (primeGaussianNearWidth m:ℝ) →
      c/Real.log (primeGaussianHyperbolicConductor m:ℝ) ≤
        primeGaussianCubicSignedRow b (primeGaussianHyperbolicConductor m) (r,p) := by
  exact ⟨sectorCutoffFloor^3/147456,by have := sectorCutoffFloor_pos;positivity,
    eventually_sectorJordanRow_lower_central⟩

private theorem nearPairs_subset_full (m : ℕ) :
    primeGaussianNearPairs m ⊆ primeProfileBand (sectorN m) ×ˢ primeProfileBand (sectorN m) := by
  rintro ⟨r,p⟩ hrp
  obtain ⟨hrP,hpP,hrl,hru,hpl,hpu,_,_⟩ := primeGaussianNearPairs_mem hrp
  change 3*sectorN m/2 < r at hrl
  change (r:ℝ) ≤ 25*sectorN m/16 at hru
  change 3*sectorN m/2 < p at hpl
  change (p:ℝ) ≤ 25*sectorN m/16 at hpu
  have hN := sectorN_pos m
  exact Finset.mem_product.mpr ⟨sector_primeProfileBand hN hrP (by linarith) (by linarith),
    sector_primeProfileBand hN hpP (by linarith) (by linarith)⟩

private theorem exists_eventually_signedVariation_lower :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ m : ℕ in atTop, ∀ b : Bool,
      A*sectorN m*sectorH m/(Real.log (sectorN m))^3 ≤ primeGaussianCubicSignedVariation b (sectorN m) := by
  obtain ⟨c,hc,hcount⟩ := exists_primeGaussianNearPairs_mass
  have hv := sectorCutoffFloor_pos
  refine ⟨c*(sectorCutoffFloor^3/147456),by positivity,?_⟩
  filter_upwards [hcount,eventually_sectorJordanRow_lower,
    sectorN_tendsto.eventually_gt_atTop 1] with m hm hrow hN1
  intro b
  have hlog : 0 < Real.log (sectorN m) := Real.log_pos hN1
  change c*sectorN m*sectorH m/(Real.log (sectorN m))^2 ≤ ((primeGaussianNearPairs m).card:ℝ) at hm
  calc
    _ = (c*sectorN m*sectorH m/(Real.log (sectorN m))^2)*
        ((sectorCutoffFloor^3/147456)/Real.log (sectorN m)) := by ring
    _ ≤ ((primeGaussianNearPairs m).card:ℝ)*((sectorCutoffFloor^3/147456)/Real.log (sectorN m)) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = ∑ _rp ∈ primeGaussianNearPairs m, (sectorCutoffFloor^3/147456)/Real.log (sectorN m) := by simp
    _ ≤ ∑ rp ∈ primeGaussianNearPairs m, primeGaussianCubicSignedRow b (sectorN m) rp :=
      Finset.sum_le_sum (fun rp hrp => hrow b rp.1 rp.2 hrp)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (nearPairs_subset_full m)
      (fun rp _ _ => sectorJordanRow_nonneg b (sectorN m) rp)

private theorem tendsto_sector_height_div_log {A : ℝ} (hA : 0 < A) :
    Tendsto (fun m : ℕ => A*sectorH m/Real.log (sectorN m)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C
  let B := max C 1
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right C 1)
  have hs := Real.isLittleO_log_id_atTop.def (c:=A/(4*B)) (by positivity)
  filter_upwards [sectorH_tendsto.eventually hs,sectorH_tendsto.eventually_ge_atTop 2]
    with m hm hm2
  have hh := sectorH_pos m
  have hlogH : 0 < Real.log (sectorH m) := Real.log_pos (by linarith)
  simp only [Real.norm_eq_abs,id,abs_of_nonneg hlogH.le,abs_of_nonneg hh.le] at hm
  have he : Real.log (sectorN m) = 4*Real.log (sectorH m) := by
    rw [← sector_four,Real.log_pow]
    norm_num
  have hlogN : 0 < Real.log (sectorN m) := by rw [he]; positivity
  apply (le_max_left C 1).trans
  apply (le_div_iff₀ hlogN).mpr
  rw [he]
  calc
    B*(4*Real.log (sectorH m)) = (4*B)*Real.log (sectorH m) := by ring
    _ ≤ (4*B)*(A/(4*B)*sectorH m) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = A*sectorH m := by field_simp

/-- Both signed parts of the COMPLETE actual noncontracting physical prime cubic grow
without bound after contraction-scale normalization. Thus its signed asymptotic cannot
be obtained from bounded one-sided or absolute majorants at that scale. -/
theorem tendsto_primeGaussianCubicSignedVariation (negative : Bool) :
    Tendsto (fun m : ℕ =>
      (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        primeGaussianCubicSignedVariation negative (primeGaussianHyperbolicConductor m)) atTop atTop := by
  obtain ⟨A,hA,hmass⟩ := exists_eventually_signedVariation_lower
  have ht := tendsto_sector_height_div_log hA
  change Tendsto (fun m : ℕ => (Real.log (sectorN m))^2/sectorN m*
    primeGaussianCubicSignedVariation negative (sectorN m)) atTop atTop
  refine tendsto_atTop.2 ?_
  intro C
  filter_upwards [hmass,(tendsto_atTop.1 ht) C,sectorN_tendsto.eventually_gt_atTop 1]
    with m hm hC hN1
  have hN := sectorN_pos m
  have hlog : 0 < Real.log (sectorN m) := Real.log_pos hN1
  have hscaled := mul_le_mul_of_nonneg_left (hm negative)
    (by positivity : 0 ≤ (Real.log (sectorN m))^2/sectorN m)
  have he : (Real.log (sectorN m))^2/sectorN m*
      (A*sectorN m*sectorH m/(Real.log (sectorN m))^3) =
        A*sectorH m/Real.log (sectorN m) := by field_simp
  rw [he] at hscaled
  exact hC.trans hscaled

end RHTower
