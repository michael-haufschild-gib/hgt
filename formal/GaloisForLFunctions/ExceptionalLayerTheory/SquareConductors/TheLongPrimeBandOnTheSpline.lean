import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheThreeQuarterProductWindow

/-!
# A long-prime band in the actual logarithmic-stencil row

Use the largest short-prime, short-complement and lower-product cutoffs
on the whole spline support. Beyond all three, a pair enters the row at
its product and stays there. Splitting by the logarithmic stencil gives
one horizon interval per pair and per stencil.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Logarithmic stencil cutoff at the prime-count horizon. -/
def splineStencilCutoff (k : ℕ) := ⌊1+Real.log k⌋₊
/-- Common upper endpoint for the small first primes on horizons through L. -/
def splineFirstPrimeCutoff (L : ℕ) := max (2*(splineStencilCutoff L+1)) ⌊(L:ℝ)^(1/200:ℝ)⌋₊
/-- Above the common lower product cutoff and above every short complement. -/
def splineBandPair (L p v : ℕ) : Prop :=
  productLower (splineStencilCutoff L) L < p*v ∧ ⌊(L:ℝ)^(1/10000:ℝ)⌋₊ < v

private instance (L p v : ℕ) : Decidable (splineBandPair L p v) := inferInstanceAs (Decidable (_ ∧ _))

private theorem splineStencilCutoff_mono {k L : ℕ} (hk : 0<k) (hkL : k≤L) : splineStencilCutoff k≤splineStencilCutoff L :=
  Nat.floor_mono (add_le_add (le_refl (1:ℝ)) (Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkL)))

private theorem splineStencilCutoff_pos (k : ℕ) : 1≤splineStencilCutoff k :=
  (Nat.one_le_floor_iff _).mpr (le_add_of_nonneg_right (Real.log_natCast_nonneg k))

private theorem splineStencilCutoff_cell {k : ℕ} (hk : 0<k) (d : ℕ) : splineStencilCutoff k=d ↔
    ⌈Real.exp ((d:ℝ)-1)⌉₊ ≤ k ∧ k < ⌈Real.exp (d:ℝ)⌉₊ := by
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
  rw [splineStencilCutoff,Nat.floor_eq_iff (by have := Real.log_natCast_nonneg k; positivity),Nat.ceil_le,Nat.lt_ceil,
    ←Real.le_log_iff_exp_le hk',←Real.log_lt_iff_lt_exp hk']
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- The coprime long-prime band below U, on the support through L. -/
def splinePrimeBand (L U k : ℕ) : ℝ :=
  clippedPrimeProducts (splineStencilCutoff k) (splineStencilCutoff k) (splineFirstPrimeCutoff L) U
    (fun p v => p*v) (fun p v => if splineBandPair L p v then L+1 else 0) k

/-- Every contributing pair belongs to the corresponding two filtered
sums defining the surviving PVC product, with the same divided horizon. -/
theorem splinePrimeBand_mem_remaining {L U k p v : ℕ} (hk : 0<k) (hkL : k≤L)
    (hp : p ∈ (Ioc (splineFirstPrimeCutoff L) U).filter Nat.Prime)
    (hv : v ∈ (Icc 1 (U/p)).filter (p.Coprime ·))
    (hactive : p*v ≤ k ∧ k < (if splineBandPair L p v then L+1 else 0)) :
    let D := splineStencilCutoff k
    let Y := productLower D k
    p ∈ (Ioc (max (2*(D+1)) ⌊(k:ℝ)^(1/200:ℝ)⌋₊) k).filter Nat.Prime ∧
    v ∈ (((Ioc (Y/p) (k/p)).filter (p.Coprime ·)).filter
      (fun v => ¬(v ∈ shortComplement D k ∧ p ∈ reciprocalProductPrimes D k Y v))) := by
  intro D Y
  obtain ⟨hpS,hprime⟩ := mem_filter.mp hp
  obtain ⟨hvS,hcop⟩ := mem_filter.mp hv
  have hv₀ := (mem_Icc.mp hvS).1
  have hpair : splineBandPair L p v := by
    by_contra hh
    simpa only [if_neg hh,Nat.not_lt_zero] using hactive.2
  have hdk := splineStencilCutoff_mono hk hkL
  have hr (s : ℝ) (hs : 0≤s) : ⌊(k:ℝ)^s⌋₊ ≤ ⌊(L:ℝ)^s⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkL) hs)
  have hcut : max (2*(D+1)) ⌊(k:ℝ)^(1/200:ℝ)⌋₊ ≤ splineFirstPrimeCutoff L :=
    max_le_max (Nat.mul_le_mul_left 2 (Nat.succ_le_succ hdk)) (hr _ (by norm_num))
  have hY : Y ≤ productLower (splineStencilCutoff L) L :=
    min_le_min hkL (Nat.mul_le_mul (Nat.succ_le_succ hdk)
      (Nat.floor_mono (Real.sqrt_le_sqrt (by exact_mod_cast hkL))))
  refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hcut.trans_lt (mem_Ioc.mp hpS).1,
    (Nat.le_mul_of_pos_right p hv₀).trans hactive.1⟩,hprime⟩,mem_filter.mpr ⟨mem_filter.mpr ⟨?_,hcop⟩,?_⟩⟩
  · exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hprime.pos).mpr
        (by simpa only [Nat.mul_comm v p] using hY.trans_lt hpair.1),
      (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa only [Nat.mul_comm v p] using hactive.1)⟩
  · intro h
    exact hpair.2.not_ge ((mem_Ioc.mp h.1).2.trans (hr _ (by norm_num)))

private def cellRow (L U d : ℕ) :=
  clippedPrimeProducts d d (splineFirstPrimeCutoff L) U
    (fun p v => max (p*v) ⌈Real.exp ((d:ℝ)-1)⌉₊)
    (fun p v => if splineBandPair L p v then ⌈Real.exp (d:ℝ)⌉₊ else 0)

private theorem cellRow_eq {k L : ℕ} (hk : 0<k) (hkL : k≤L) (U d : ℕ) :
    cellRow L U d k = if splineStencilCutoff k=d then splinePrimeBand L U k else 0 := by
  by_cases hd : splineStencilCutoff k=d
  · rw [if_pos hd,cellRow,splinePrimeBand,hd]
    unfold clippedPrimeProducts ordinaryFactorTail
    apply sum_congr rfl; intro p _
    congr 1
    apply sum_congr rfl; intro v _
    obtain ⟨hl,hu⟩ := (splineStencilCutoff_cell hk d).mp hd
    have htop : k<L+1 := Nat.lt_succ_of_le hkL
    by_cases hb : splineBandPair L p v <;> simp only [hb,if_true,if_false,max_le_iff,hl,hu,htop,
      and_true,Nat.not_lt_zero,and_false]
  · rw [if_neg hd,cellRow,clippedPrimeProducts,ordinaryFactorTail]
    apply sum_eq_zero; intro p _
    apply mul_eq_zero_of_right
    apply sum_eq_zero; intro v _
    apply mul_eq_zero_of_right
    apply if_neg
    rintro ⟨hl,hu⟩
    by_cases hb : splineBandPair L p v
    · exact hd ((splineStencilCutoff_cell hk d).mpr ⟨(le_max_right ..).trans hl,by simpa only [if_pos hb] using hu⟩)
    · simpa only [if_neg hb,Nat.not_lt_zero] using hu

private theorem band_reading_eq (n U : ℕ) :
    let L := splineHorizon n
    splineCountReading n (splinePrimeBand L U) =
      ∑ d ∈ Icc 1 (splineStencilCutoff L), splineCountReading n (cellRow L U d) := by
  intro L
  unfold splineCountReading
  rw [sum_comm]
  apply sum_congr rfl; intro k hk
  rw [←sum_mul]
  congr 1
  obtain ⟨hk₀,hkL⟩ := mem_Icc.mp hk
  simp only [cellRow_eq hk₀ hkL, sum_ite_eq,if_pos (mem_Icc.mpr ⟨splineStencilCutoff_pos k,splineStencilCutoff_mono hk₀ hkL⟩)]

/-- All the selected long primes together cost five stencil logarithms
and one Mertens logarithm, uniformly through the three-quarter product scale. -/
theorem long_prime_band_spline_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n U : ℕ}, 0<n → 1≤U → U≤n*n.sqrt →
      |splineCountReading n (splinePrimeBand (splineHorizon n) U)| ≤
        C*(1+Real.log (splineHorizon n))^5*(1+Real.log U) := by
  obtain ⟨C,hC,h⟩ := spline_three_quarter_product_bound
  obtain ⟨M,hM,hm⟩ := mass_uniform
  let B := C*(2*(1+2*M))*(125*(1+M)*(128*129))
  refine ⟨B,by dsimp [B]; positivity,fun {n U} hn hu hcut => ?_⟩
  let L := splineHorizon n
  let H := 1+Real.log L
  have hH : 1≤H := le_add_of_nonneg_right (Real.log_natCast_nonneg L)
  have hH₀ : 0≤H := zero_le_one.trans hH
  have hU := Real.log_natCast_nonneg U
  have hK : (splineStencilCutoff L:ℝ) ≤ H := Nat.floor_le (zero_le_one.trans hH)
  have one (d : ℕ) (hd : d ∈ Icc 1 (splineStencilCutoff L)) :
      |splineCountReading n (cellRow L U d)| ≤ B*H^4*(1+Real.log U) := by
    obtain ⟨hd₁,hdK⟩ := mem_Icc.mp hd
    have hdH := (show (d:ℝ)≤splineStencilCutoff L by exact_mod_cast hdK).trans hK
    have hmass := hm d hd₁
    have hnext := hm (d+1) (Nat.succ_pos d)
    push_cast at hnext
    have h₁ : 2*(1+mass (d+1)) ≤ 2*(1+2*M)*H := by
      linarith only [hnext,hH,mul_le_mul_of_nonneg_left hdH hM,le_mul_of_one_le_right hM hH]
    have h₂ : 1+mass d ≤ (1+M)*H := by
      linarith only [hmass,hH,mul_le_mul_of_nonneg_left hdH hM]
    have h₃ : 128*(128*(d:ℝ)^2+1) ≤ (128*129)*H^2 := by
      linarith only [pow_le_pow_left₀ (Nat.cast_nonneg d) hdH 2,one_le_pow₀ (n := 2) hH]
    have hpos := (abs_nonneg _).trans (abs_prefix_le_mass hd₁ 0)
    apply (h hn hd₁ hu hcut d (splineFirstPrimeCutoff L) _ _).trans
    have hprod := mul_le_mul (mul_le_mul_of_nonneg_left h₁ hC)
      (mul_le_mul (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0:ℝ) ≤ 125)) h₃ (by positivity) (by positivity))
      (by positivity) (by positivity)
    exact (mul_le_mul_of_nonneg_right hprod (by positivity : 0≤1+Real.log U)).trans_eq (by dsimp [B]; ring)
  rw [band_reading_eq]
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum one).trans _)
  rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
  have hB : 0≤B := by dsimp [B]; positivity
  exact (mul_le_mul_of_nonneg_right hK (by positivity : 0≤B*H^4*(1+Real.log U))).trans_eq (by ring)

/-- The signed remainder after deleting the long-prime band at the full
three-quarter cutoff. -/
def outsideSplinePrimeBand (n : ℕ) : ℝ :=
  splineCountReading n (fun k => longPrimeRow k-splinePrimeBand (splineHorizon n) (n*n.sqrt) k)

private theorem square_le_horizon (n : ℕ) : n^2 ≤ splineHorizon n := by
  obtain ⟨h₁,_,h₂⟩ := GaloisForLFunctions.CountingHolography.Sections.successorSquareWindowScale_bounds n
  have h : n^2 ≤ GaloisForLFunctions.CountingHolography.Sections.windowEnd ((2*n+1)^2+1) := by
    exact_mod_cast h₁.trans h₂
  exact h.trans (Nat.le_mul_of_pos_left _ (by decide : 0<3))

/-- After deleting the indicated band the full dyadic contact differs from
the remaining signed products by at most six logarithms on every conductor. -/
theorem dyadicPrimeContact_outside_band :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0<n →
      |GaloisForLFunctions.CountingHolography.Sections.dyadicPrimeContact n-outsideSplinePrimeBand n| ≤
        C*(1+Real.log (splineHorizon n))^6 := by
  obtain ⟨A,hA,ha⟩ := dyadicPrimeContact_long_products
  obtain ⟨B,hB,hb⟩ := long_prime_band_spline_bound
  refine ⟨A+B,add_nonneg hA hB,fun {n} hn => ?_⟩
  let L := splineHorizon n
  let U := n*n.sqrt
  let H := 1+Real.log L
  have hU : 0<U := Nat.mul_pos hn (Nat.sqrt_pos.mpr hn)
  have hq : U ≤ L := (Nat.mul_le_mul_left n (Nat.sqrt_le_self n)).trans
    (by simpa only [sq] using square_le_horizon n)
  have hlog : 1+Real.log U ≤ H := add_le_add (le_refl (1:ℝ))
    (Real.log_le_log (by exact_mod_cast hU) (by exact_mod_cast hq))
  have hH : 0≤H := by dsimp [H]; have := Real.log_natCast_nonneg L; positivity
  have he : outsideSplinePrimeBand n = splineCountReading n longPrimeRow-
      splineCountReading n (splinePrimeBand L U) := by
    unfold outsideSplinePrimeBand splineCountReading
    simp only [sub_mul,sum_sub_distrib,L,U]
  rw [he,show ∀ a b c : ℝ, a-(b-c)=(a-b)+c from fun _ _ _ => by ring]
  apply (abs_add_le _ _).trans ((add_le_add (ha hn) (hb hn hU le_rfl)).trans _)
  have hh := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB (pow_nonneg hH 5))
  change A*H^6+B*H^5*(1+Real.log U) ≤ (A+B)*H^6
  linarith only [hh]

private theorem logarithmic_allowance {s : ℝ} (hs : 0<s) :
    ∃ C : ℝ, 0≤C ∧ ∀ {n : ℕ}, 0<n →
      (1+Real.log (splineHorizon n))^6 ≤ C*((n:ℝ)+1)^(2*s) := by
  obtain ⟨A,hA,ha⟩ := GaloisForLFunctions.CountingHolography.Sections.successorSquare_window_bound
  let a := s/6
  have hapos : 0<a := div_pos hs (by norm_num)
  have hA₀ := zero_le_one.trans hA
  let B := (1+1/a)^6
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨B*A^(2*s),by positivity,fun {n} hn => ?_⟩
  let L := splineHorizon n
  have hL : (1:ℝ)≤L := by exact_mod_cast (pow_pos hn 2).trans_le (square_le_horizon n)
  have h₁ := Real.one_le_rpow hL hapos.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hL) hapos
  have hbase : 1+Real.log L ≤ (1+1/a)*(L:ℝ)^a := by
    calc _ ≤ (L:ℝ)^a+(L:ℝ)^a/a := add_le_add h₁ hl
         _ = _ := by ring
  have hpow : ((L:ℝ)^a)^6=(L:ℝ)^s := by
    rw [←Real.rpow_natCast _ 6,←Real.rpow_mul (zero_le_one.trans hL)]
    congr 1; dsimp [a]; norm_num <;> ring
  have hscale : ((A*n)^2)^s=A^(2*s)*(n:ℝ)^(2*s) := by
    rw [←Real.rpow_two,←Real.rpow_mul (mul_nonneg hA₀ (Nat.cast_nonneg n)),Real.mul_rpow hA₀ (Nat.cast_nonneg n)]
  apply (pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg L)) hbase 6).trans
  rw [mul_pow,hpow]
  apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg L) (ha hn) hs.le) hB).trans
  rw [hscale,←mul_assoc]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg n)
    (le_add_of_nonneg_right zero_le_one) (mul_nonneg two_pos.le hs.le)) (by positivity)

/-- At every positive subcritical exponent, a one-sided estimate for the
remaining products retains the exact strip receiver. -/
theorem width_iff_outside_spline_band {s : ℝ} (hs : 0<s) (hs' : s<1/2) :
    SquareRootThreshold.zetaZeroWidth ≤ s ↔ ∃ C : ℝ, ∀ n : ℕ, 0<n →
      outsideSplinePrimeBand n ≤ C*((n:ℝ)+1)^(2*s) := by
  obtain ⟨B,hB,h⟩ := dyadicPrimeContact_outside_band
  obtain ⟨A,_,ha⟩ := logarithmic_allowance hs
  rw [GaloisForLFunctions.CountingHolography.Sections.zetaZeroWidth_le_iff_dyadicPrimeContact hs.le hs']
  constructor <;> rintro ⟨C,hC⟩ <;> refine ⟨C+B*A,fun n hn => ?_⟩
  · linarith only [hC n hn,(abs_le.mp (h hn)).1,mul_le_mul_of_nonneg_left (ha hn) hB]
  · linarith only [hC n hn,(abs_le.mp (h hn)).2,mul_le_mul_of_nonneg_left (ha hn) hB]

#print axioms splinePrimeBand_mem_remaining
#print axioms long_prime_band_spline_bound
#print axioms dyadicPrimeContact_outside_band
#print axioms width_iff_outside_spline_band
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
