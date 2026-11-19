import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLowerIntegerPrefixAtTheMovingEdge

/-!
# Prime excess on a record interval

A record of the Chebyshev error minus a power bounds every earlier endpoint
from above. Starting at the minimum in a short multiplicative interval puts
all partial increments between zero and the full positive increment.
-/

noncomputable section
open Filter Set Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

private def integerExcess (n : ℕ) : ℝ := Chebyshev.psi n-n

private theorem integerExcess_sub {a j : ℕ} (h : a ≤ j) :
    centeredAbelPrefix a j = integerExcess j-integerExcess a := by
  have hψ := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc ((Nat.cast_le (α := ℝ)).mpr h)
  simp only [Nat.floor_natCast] at hψ
  rw [centeredAbelPrefix,Finset.sum_sub_distrib,← hψ,Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul,
    mul_one,Nat.cast_sub h,integerExcess,integerExcess]
  ring

private theorem unbounded_integer_excess_sub_power {b : ℝ} (hb : 0 < b) (hΘ : b < zeroReSup)
    (A : ℝ) : ∃ n : ℕ, A < integerExcess n-(n:ℝ)^b := by
  let d := (b+zeroReSup)/2
  have hd : b<d := by dsimp only [d]; linarith
  have htop := (frequently_rpow_lt_chebyshevPsi_sub (show d<zeroReSup by dsimp only [d]; linarith))
  obtain ⟨x,⟨⟨hx,hbig⟩,hgain⟩,hx1⟩ := (((htop.and_eventually
    ((tendsto_rpow_atTop hb).eventually_gt_atTop A)).and_eventually
    ((tendsto_rpow_atTop (sub_pos.mpr hd)).eventually_gt_atTop 2)).and_eventually
    (eventually_gt_atTop (1:ℝ))).exists
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hpow : x^b*x^(d-b)=x^d := by rw [← Real.rpow_add hx0]; congr 1; ring
  have htwice := mul_lt_mul_of_pos_left hgain (Real.rpow_pos_of_pos hx0 b)
  rw [hpow] at htwice
  have hfloor := Nat.floor_le hx0.le
  have hmono := Real.rpow_le_rpow (Nat.cast_nonneg ⌊x⌋₊) hfloor hb.le
  refine ⟨⌊x⌋₊,?_⟩
  rw [Chebyshev.psi_eq_psi_coe_floor x] at hx
  dsimp only [integerExcess]
  linarith only [hx,hbig,htwice,hfloor,hmono]

private theorem frequently_excess_record {b : ℝ} (hb : 0 < b) (hΘ : b < zeroReSup) :
    ∃ᶠ N : ℕ in atTop, ∀ j : ℕ, j ≤ N →
      (N:ℝ)^b-(j:ℝ)^b ≤ integerExcess N-integerExcess j := by
  classical
  let f := fun j : ℕ => integerExcess j-(j:ℝ)^b
  rw [frequently_atTop]
  intro B
  obtain ⟨j,hj,hmax⟩ := (Finset.Iic B).exists_max_image f ⟨B,Finset.mem_Iic.mpr le_rfl⟩
  obtain ⟨u,hu⟩ := unbounded_integer_excess_sub_power hb hΘ (f j)
  obtain ⟨N,hN,hrec⟩ := (Finset.Iic u).exists_max_image f ⟨u,Finset.mem_Iic.mpr le_rfl⟩
  have hlarge : B ≤ N := by
    by_contra! hn
    exact (hu.trans_le (hrec u (Finset.mem_Iic.mpr le_rfl))).not_ge
      (hmax N (Finset.mem_Iic.mpr hn.le))
  refine ⟨N,hlarge,fun i hi => ?_⟩
  have hr := hrec i (Finset.mem_Iic.mpr (hi.trans (Finset.mem_Iic.mp hN)))
  dsimp only [f] at hr
  linarith only [hr]

/-- On arbitrarily late integer intervals inside any fixed terminal fraction
of N, every prefix stays between zero and the terminal prime excess. The latter
exceeds a fixed positive multiple of N^b for every positive b below Θ. -/
theorem frequently_centered_prime_record_band {b q : ℝ} (hb : 0 < b) (hΘ : b < zeroReSup)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop, ∃ L : ℕ, 0 < L ∧ L ≤ N ∧ q*N ≤ L ∧
      c*(N:ℝ)^b ≤ centeredAbelPrefix L N ∧
      ∀ j : ℕ, L ≤ j → j ≤ N → 0 ≤ centeredAbelPrefix L j ∧
        centeredAbelPrefix L j ≤ centeredAbelPrefix L N := by
  classical
  let r := (q+1)/2
  have hr0 : 0 < r := by dsimp only [r]; linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hgap : 0 < r-q := by dsimp only [r]; linarith
  refine ⟨1-r^b,sub_pos.mpr (Real.rpow_lt_one hr0.le hr1 hb),?_⟩
  have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (1/(r-q))
  apply ((frequently_excess_record hb hΘ).and_eventually hlarge).mono
  rintro N ⟨hrecord,hN⟩
  have hN0 : 0 < (N:ℝ) := (one_div_pos.mpr hgap).trans hN
  let J := ⌊r*N⌋₊
  have hJ : (J:ℝ) ≤ r*N := Nat.floor_le (mul_nonneg hr0.le hN0.le)
  have hJN : J ≤ N := Nat.cast_le.mp (hJ.trans (mul_le_of_le_one_left hN0.le hr1.le))
  have hqJ : q*N ≤ J := by
    have h := (div_lt_iff₀ hgap).mp hN
    nlinarith only [h,Nat.lt_floor_add_one (r*N)]
  obtain ⟨L,hL,hmin⟩ := (Finset.Icc J N).exists_min_image integerExcess
    ⟨J,Finset.mem_Icc.mpr ⟨le_rfl,hJN⟩⟩
  obtain ⟨hJL,hLN⟩ := Finset.mem_Icc.mp hL
  have hqL := hqJ.trans (Nat.cast_le.mpr hJL)
  have hL0 : 0<L := Nat.cast_pos.mp ((mul_pos hq hN0).trans_le hqL)
  refine ⟨L,hL0,hLN,hqL,?_,fun j hLj hjN => ?_⟩
  · have hJb := Real.rpow_le_rpow (Nat.cast_nonneg J) hJ hb.le
    rw [Real.mul_rpow hr0.le hN0.le] at hJb
    have h := hrecord J hJN
    have hminJ := hmin J (Finset.mem_Icc.mpr ⟨le_rfl,hJN⟩)
    rw [integerExcess_sub hLN]
    linarith only [hJb,h,hminJ]
  · have hminj := hmin j (Finset.mem_Icc.mpr ⟨hJL.trans hLj,hjN⟩)
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg j) (Nat.cast_le.mpr hjN) hb.le
    have hmaxj := hrecord j hjN
    rw [integerExcess_sub hLj,integerExcess_sub hLN]
    exact ⟨sub_nonneg.mpr hminj,by linarith only [hp,hmaxj]⟩

/-- If every signed prefix lies between zero and its endpoint, the total
downward correction to the endpoint-weight reading is at most the endpoint
excess times the total absolute change of the weights. -/
theorem record_band_weighted_lower (w : ℕ → ℝ) {L N : ℕ} (hLN : L ≤ N) {v : ℝ}
    (hp : ∀ j, L ≤ j → j ≤ N → 0 ≤ centeredAbelPrefix L j ∧
      centeredAbelPrefix L j ≤ centeredAbelPrefix L N)
    (hw : ∀ j, L ≤ j → j < N → |w (j+1)-w j| ≤ v) :
    (w N-(N-L:ℕ)*v)*centeredAbelPrefix L N ≤
      ∑ n ∈ Finset.Ioc L N, (vonMangoldt n-1)*w n := by
  have hcost : ∑ j ∈ Finset.Ico L N, -(centeredAbelPrefix L N*v) ≤
      ∑ j ∈ Finset.Ico L N, centeredAbelPrefix L j*(w j-w (j+1)) := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨ha,hb⟩ := Finset.mem_Ico.mp hj
    obtain ⟨h0,h1⟩ := hp j ha hb.le
    have h := mul_le_mul (h1) (hw j ha hb) (abs_nonneg _) (h0.trans h1)
    rw [abs_sub_comm] at h
    have hh := neg_abs_le (w j-w (j+1))
    linarith only [h,mul_le_mul_of_nonneg_left hh h0]
  rw [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul] at hcost
  rw [centeredAbelPrefix_by_parts w (le_refl L) hLN,
    show centeredAbelPrefix L L=0 by simp [centeredAbelPrefix],mul_zero,sub_zero]
  linarith only [hcost]

#print axioms frequently_centered_prime_record_band
#print axioms record_band_weighted_lower
end GaloisForLFunctions.ExclusionOfTheCriticalState
