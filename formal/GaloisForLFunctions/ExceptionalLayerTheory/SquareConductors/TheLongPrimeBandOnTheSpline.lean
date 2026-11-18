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

private def logCut (k : ℕ) := ⌊1+Real.log k⌋₊
private def firstCut (L : ℕ) := max (2*(logCut L+1)) ⌊(L:ℝ)^(1/200:ℝ)⌋₊
private def bandPair (L p v : ℕ) : Prop :=
  productLower (logCut L) L < p*v ∧ ⌊(L:ℝ)^(1/10000:ℝ)⌋₊ < v

private instance (L p v : ℕ) : Decidable (bandPair L p v) := inferInstanceAs (Decidable (_ ∧ _))

private theorem logCut_mono {k L : ℕ} (hk : 0<k) (hkL : k≤L) : logCut k≤logCut L :=
  Nat.floor_mono (add_le_add_left (Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkL)) 1)

private theorem logCut_pos (k : ℕ) : 1≤logCut k :=
  (Nat.one_le_floor_iff _).mpr (le_add_of_nonneg_right (Real.log_natCast_nonneg k))

private theorem logCut_cell {k : ℕ} (hk : 0<k) (d : ℕ) : logCut k=d ↔
    ⌈Real.exp ((d:ℝ)-1)⌉₊ ≤ k ∧ k < ⌈Real.exp (d:ℝ)⌉₊ := by
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
  rw [logCut,Nat.floor_eq_iff (by have := Real.log_natCast_nonneg k; positivity),Nat.ceil_le,Nat.lt_ceil,
    ←Real.le_log_iff_exp_le hk',←Real.log_lt_iff_lt_exp hk']
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- The coprime long-prime band below U, on the support through L. -/
def splinePrimeBand (L U k : ℕ) : ℝ :=
  clippedPrimeProducts (logCut k) (logCut k) (firstCut L) U
    (fun p v => p*v) (fun p v => if bandPair L p v then L+1 else 0) k

/-- Every contributing pair belongs to the corresponding two filtered
sums defining the surviving PVC product, with the same divided horizon. -/
theorem splinePrimeBand_mem_remaining {L U k p v : ℕ} (hk : 0<k) (hkL : k≤L)
    (hp : p ∈ (Ioc (firstCut L) U).filter Nat.Prime)
    (hv : v ∈ (Icc 1 (U/p)).filter (p.Coprime ·))
    (hactive : p*v ≤ k ∧ k < (if bandPair L p v then L+1 else 0)) :
    let D := logCut k
    let Y := productLower D k
    p ∈ (Ioc (max (2*(D+1)) ⌊(k:ℝ)^(1/200:ℝ)⌋₊) k).filter Nat.Prime ∧
    v ∈ (((Ioc (Y/p) (k/p)).filter (p.Coprime ·)).filter
      (fun v => ¬(v ∈ shortComplement D k ∧ p ∈ reciprocalProductPrimes D k Y v))) := by
  intro D Y
  obtain ⟨hpS,hprime⟩ := mem_filter.mp hp
  obtain ⟨hvS,hcop⟩ := mem_filter.mp hv
  have hv₀ := (mem_Icc.mp hvS).1
  have hpair : bandPair L p v := by
    by_contra hh
    simpa only [if_neg hh,Nat.not_lt_zero] using hactive.2
  have hdk := logCut_mono hk hkL
  have hr (s : ℝ) (hs : 0≤s) : ⌊(k:ℝ)^s⌋₊ ≤ ⌊(L:ℝ)^s⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkL) hs)
  have hcut : max (2*(D+1)) ⌊(k:ℝ)^(1/200:ℝ)⌋₊ ≤ firstCut L :=
    max_le_max (Nat.mul_le_mul_left 2 (Nat.succ_le_succ hdk)) (hr _ (by norm_num))
  have hY : Y ≤ productLower (logCut L) L :=
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
  clippedPrimeProducts d d (firstCut L) U
    (fun p v => max (p*v) ⌈Real.exp ((d:ℝ)-1)⌉₊)
    (fun p v => if bandPair L p v then ⌈Real.exp (d:ℝ)⌉₊ else 0)

private theorem cellRow_eq {k L : ℕ} (hk : 0<k) (hkL : k≤L) (U d : ℕ) :
    cellRow L U d k = if logCut k=d then splinePrimeBand L U k else 0 := by
  by_cases hd : logCut k=d
  · rw [if_pos hd,cellRow,splinePrimeBand,hd]
    unfold clippedPrimeProducts ordinaryFactorTail
    apply sum_congr rfl; intro p _
    congr 1
    apply sum_congr rfl; intro v _
    obtain ⟨hl,hu⟩ := (logCut_cell hk d).mp hd
    have htop : k<L+1 := Nat.lt_succ_of_le hkL
    by_cases hb : bandPair L p v <;> simp only [hb,if_true,if_false,max_le_iff,hl,hu,htop,
      and_true,Nat.not_lt_zero,and_false]
  · rw [if_neg hd,cellRow,clippedPrimeProducts,ordinaryFactorTail]
    apply sum_eq_zero; intro p _
    apply mul_eq_zero_of_right
    apply sum_eq_zero; intro v _
    apply mul_eq_zero_of_right
    apply if_neg
    rintro ⟨hl,hu⟩
    by_cases hb : bandPair L p v
    · exact hd ((logCut_cell hk d).mpr ⟨(le_max_right ..).trans hl,by simpa only [if_pos hb] using hu⟩)
    · simpa only [if_neg hb,Nat.not_lt_zero] using hu

private theorem band_reading_eq (n U : ℕ) :
    let L := splineHorizon n
    splineCountReading n (splinePrimeBand L U) =
      ∑ d ∈ Icc 1 (logCut L), splineCountReading n (cellRow L U d) := by
  intro L
  unfold splineCountReading
  rw [sum_comm]
  apply sum_congr rfl; intro k hk
  rw [←sum_mul]
  congr 1
  obtain ⟨hk₀,hkL⟩ := mem_Icc.mp hk
  simp only [cellRow_eq hk₀ hkL, sum_ite_eq,if_pos (mem_Icc.mpr ⟨logCut_pos k,logCut_mono hk₀ hkL⟩)]

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
  have hU := Real.log_natCast_nonneg U
  have hK : (logCut L:ℝ) ≤ H := Nat.floor_le (zero_le_one.trans hH)
  have one (d : ℕ) (hd : d ∈ Icc 1 (logCut L)) :
      |splineCountReading n (cellRow L U d)| ≤ B*H^4*(1+Real.log U) := by
    obtain ⟨hd₁,hdK⟩ := mem_Icc.mp hd
    have hdH := (show (d:ℝ)≤logCut L by exact_mod_cast hdK).trans hK
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
    apply (h hn hd₁ hu hcut d (firstCut L) _ _).trans
    have hprod := mul_le_mul (mul_le_mul_of_nonneg_left h₁ hC)
      (mul_le_mul (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0:ℝ) ≤ 125)) h₃ (by positivity) (by positivity))
      (by positivity) (by positivity)
    exact (mul_le_mul_of_nonneg_right hprod (by positivity : 0≤1+Real.log U)).trans_eq (by dsimp [B]; ring)
  rw [band_reading_eq]
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum one).trans _)
  rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
  have hB : 0≤B := by dsimp [B]; positivity
  exact (mul_le_mul_of_nonneg_right hK (by positivity : 0≤B*H^4*(1+Real.log U))).trans_eq (by ring)

#print axioms splinePrimeBand_mem_remaining
#print axioms long_prime_band_spline_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
