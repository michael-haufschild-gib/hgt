import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PhaseRetrievalFromSuccessiveLogWindows
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimitiveSpectrumOfTheMoebiusGram
import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyMellin
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.BlaschkeLocalizedClockAsymptotic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The nearest-neighbor part of the logarithmic window spectrum

The separation mechanism in Gabet, Ferreira Da Costa and Lee, Lemma 4.1,
removes distant frequencies. On integer log frequencies, the next band still
has an exact description: below twice the inverse cutoff, every surviving
off-diagonal term joins consecutive integers. The last such occupied edge
determines the first departure from diagonal energy.
-/
noncomputable section
open Finset Complex Filter
open scoped Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

/-- Separation of the consecutive log frequencies at k and k+1. -/
def adjacentLogGap (k : ℕ) := Real.log (k+1:ℕ)-Real.log k

private theorem log_gap_lower {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    ((j:ℝ)-(i:ℝ))/(j:ℝ)≤Real.log j-Real.log i := by
  have hi' : 0<(i:ℝ) := by exact_mod_cast hi
  have hj' : 0<(j:ℝ) := by exact_mod_cast hj
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hj' hi')
  rw [inv_div,Real.log_div hj'.ne' hi'.ne'] at hh
  simpa only [sub_div,div_self hj'.ne'] using hh

private theorem row_first_neighbors (a : ℕ → ℂ) (N : ℕ) {d : ℝ}
    (hd : 0≤d) (hwidth : d*((N+2:ℕ):ℝ)≤2) :
    row a (N+1) d = ‖a (N+2)‖^2*d+
      2*gram (a (N+2)) (a (N+1))*max (d-adjacentLogGap (N+1)) 0 := by
  rw [row_spectrum,max_eq_left hd]
  have hsum : (∑ m∈Icc 1 (N+1),gram (a (N+2)) (a m)*max (d-gap (N+1) m) 0) =
      gram (a (N+2)) (a (N+1))*max (d-adjacentLogGap (N+1)) 0 := by
    rw [sum_eq_single (N+1)]
    · rfl
    · intro m hm hne
      obtain ⟨hpos,hupper⟩ := mem_Icc.mp hm
      have hg : d≤gap (N+1) m := by
        refine le_trans ?_ (log_gap_lower (i:=m) (j:=N+2) hpos (by omega))
        apply (le_div_iff₀ (Nat.cast_pos.mpr (by omega : 0<N+2) : 0<((N+2:ℕ):ℝ))).mpr
        have htwo : m+2≤N+2 := by omega
        have htwo' : (m:ℝ)+2≤((N+2:ℕ):ℝ) := by exact_mod_cast htwo
        linarith only [htwo',hwidth]
      rw [max_eq_right (sub_nonpos.mpr hg),mul_zero]
    · simp
  rw [hsum,mul_assoc]

/-- All off-diagonal energy through bandwidth 2/(N+1) comes from
adjacent integers. Their signed coefficients and triangular weights are exact. -/
theorem log_window_adjacent_band (a : ℕ → ℂ) (N : ℕ) {d : ℝ}
    (hd : 0≤d) (hwidth : d*((N+1:ℕ):ℝ)≤2) :
    energy a (N+1) d =
      d*(∑ j∈range (N+1),‖a (j+1)‖^2)+
        2*∑ j∈range N,gram (a (j+2)) (a (j+1))*max (d-adjacentLogGap (j+1)) 0 := by
  induction N with
  | zero =>
    simp [energy,RHTower.Sieve.integral_normSq_logWindowSum,hd,mul_comm]
    left
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  | succ n ih =>
    have hsmall : d*((n+1:ℕ):ℝ)≤2 := (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Nat.le_succ (n+1))) hd).trans hwidth
    have he := row_first_neighbors a n hd hwidth
    unfold row at he
    rw [ih hsmall] at he
    rw [Finset.sum_range_succ (fun j => ‖a (j+1)‖^2) (n+1),
      Finset.sum_range_succ (fun j => gram (a (j+2)) (a (j+1))*max (d-adjacentLogGap (j+1)) 0) n]
    linear_combination he

/-- Positive log gap in ratio form. -/
theorem adjacent_as_ratio {k : ℕ} (hk : 0<k) :
    adjacentLogGap k=Real.log (((k:ℝ)+1)/(k:ℝ)) := by
  rw [Real.log_div (by positivity) (Nat.cast_pos.mpr hk).ne']
  simp [adjacentLogGap]

/-- Consecutive log gaps strictly decrease. -/
theorem adjacent_log_gap_strict {i j : ℕ} (hi : 0 < i) (hij : i < j) :
    adjacentLogGap j<adjacentLogGap i := by
  have hj := hi.trans hij
  rw [adjacent_as_ratio hi,adjacent_as_ratio hj]
  apply Real.log_lt_log (by positivity)
  rw [div_lt_div_iff₀ (Nat.cast_pos.mpr hj) (Nat.cast_pos.mpr hi)]
  have hcast : (i:ℝ)<j := by exact_mod_cast hij
  nlinarith only [hcast]

/-- Reciprocal endpoints bound the logarithmic gap. -/
theorem adjacent_log_gap_bounds {k : ℕ} (hk : 0<k) :
    1/((k:ℝ)+1)≤adjacentLogGap k ∧ adjacentLogGap k≤1/(k:ℝ) := by
  refine ⟨?_,?_⟩
  · simpa [adjacentLogGap] using log_gap_lower (j:=k+1) hk (Nat.succ_pos _)
  · rw [adjacent_as_ratio hk]
    apply (Real.log_le_sub_one_of_pos (by positivity)).trans_eq
    field_simp [(Nat.cast_pos.mpr hk : 0<(k:ℝ)).ne']
    ring

/-- If the top pair is present, sampling between its spacing and the next
spacing isolates its Gram coefficient in a single full-prefix observation. -/
theorem top_pair_in_full_window (a : ℕ → ℂ) (N : ℕ) (hN : 0<N) {d : ℝ}
    (hd : adjacentLogGap (N+2)≤d) (hnext : d≤adjacentLogGap (N+1)) :
    energy a (N+3) d = d*(∑ j∈range (N+3),‖a (j+1)‖^2)+
      2*gram (a (N+3)) (a (N+2))*(d-adjacentLogGap (N+2)) := by
  have hd0 : 0≤d := (by positivity : 0≤1/(((N+2:ℕ):ℝ)+1)).trans
    ((adjacent_log_gap_bounds (k:=N+2) (by omega)).1.trans hd)
  have hcut : d*((N+3:ℕ):ℝ)≤2 := by
    have hu := hnext.trans (adjacent_log_gap_bounds (k:=N+1) (by omega)).2
    have ht : 0<((N+1:ℕ):ℝ) := by positivity
    have h₁ := (le_div_iff₀ ht).mp hu
    have hr : ((N+3:ℕ):ℝ)≤2*((N+1:ℕ):ℝ) := by exact_mod_cast (show N+3≤2*(N+1) by omega)
    calc _ ≤ d*(2*((N+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_left hr hd0
         _ = 2*(d*((N+1:ℕ):ℝ)) := by ring
         _ ≤ 2 := by linarith only [h₁]
  rw [log_window_adjacent_band a (N+2) hd0 hcut,
    Finset.sum_range_succ (fun j => gram (a (j+2)) (a (j+1))*max (d-adjacentLogGap (j+1)) 0) (N+1)]
  rw [sum_eq_zero (fun j (hj : j∈range (N+1)) => by
    have hj' := mem_range.mp hj
    have hg : adjacentLogGap (N+1)≤adjacentLogGap (j+1) := by
      rcases eq_or_lt_of_le (show j+1≤N+1 by omega) with he|hel
      · rw [he]
      · exact (adjacent_log_gap_strict (by omega) hel).le
    rw [max_eq_right (sub_nonpos.mpr (hnext.trans hg)),mul_zero]),zero_add,
    max_eq_left (sub_nonneg.mpr hd),mul_assoc]


open _root_.RHTower.SquarefreeDiscrepancy (count error abs_error_le)
open _root_.RHTower.Sieve (squarefreeDensity)

private def occupied (n : ℕ) : ℝ := if Squarefree n then 1 else 0

private theorem occupied_eq (n : ℕ) :
    occupied n=((ArithmeticFunction.moebius n:ℤ):ℝ)^2 := by
  rw [occupied,←Int.cast_pow,ArithmeticFunction.moebius_sq]
  split <;> norm_num

private theorem count_nat (N : ℕ) : count N=∑ i∈range N,occupied (i+1) := by
  simp only [count,Nat.floor_natCast,_root_.RHTower.sum_Icc_eq_sum_range_shift,occupied_eq]

private theorem count_block (A H : ℕ) :
    count (A+H:ℕ)-count A=∑ i∈range H,occupied (A+i+1) := by
  rw [count_nat,count_nat,sum_range_add,add_sub_cancel_left]

/-- Number of adjacent squarefree pairs with left endpoint in (A,A+H]. -/
def occupiedNeighbors (A H : ℕ) := ∑ j∈range H, occupied (A+j+1)*occupied (A+j+2)

private theorem count_to_pairs (A H : ℕ) :
    2*(∑ j∈range H,occupied (A+j+1))-(H:ℝ)+occupied (A+H+1)-occupied (A+1)≤
      occupiedNeighbors A H := by
  induction H with
  | zero => simp [occupiedNeighbors]
  | succ H ih =>
    rw [Finset.sum_range_succ,Nat.cast_succ]
    have hs : occupiedNeighbors A (H+1) = occupiedNeighbors A H+
        occupied (A+H+1)*occupied (A+H+2) := Finset.sum_range_succ _ _
    rw [hs]
    have hab : occupied (A+H+1)+occupied (A+H+2)-1≤
        occupied (A+H+1)*occupied (A+H+2) := by
      unfold occupied
      split_ifs <;> norm_num
    change _ + occupied (A+H+2)-_≤_
    linarith only [ih,hab]

private theorem density_margin : 1/5<2*squarefreeDensity-1 := by
  rw [_root_.RHTower.Sieve.squarefreeDensity_eq]
  have hπ := Real.pi_lt_d2
  have hbound := mul_self_lt_mul_self Real.pi_pos.le hπ
  have hπsq : 0<Real.pi^2 := pow_pos Real.pi_pos 2
  have hd : 3/5 < 6/Real.pi^2 := (lt_div_iff₀ hπsq).mpr (by nlinarith only [hbound])
  linarith only [hd]

/-- Uniform count of occupied nearest-neighbor frequencies in any block.
The estimate only uses the square-root error in the one-point count. -/
theorem squarefree_neighbor_count_lower {A : ℕ} (hA : 0<A) (H : ℕ) :
    (2*squarefreeDensity-1)*(H:ℝ)-16*Real.sqrt (A+H:ℕ)-1≤occupiedNeighbors A H := by
  have hstart := (abs_le.mp (abs_error_le (x:=(A:ℝ)) (by exact_mod_cast hA))).2
  have hend := (abs_le.mp (abs_error_le (x:=((A+H:ℕ):ℝ)) (by exact_mod_cast (show 1≤A+H by omega)))).1
  have hsqrt := Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_add_right A H) : (A:ℝ)≤(A+H:ℕ))
  simp only [error,Nat.cast_add] at hstart hend hsqrt ⊢
  have hc := count_to_pairs A H
  rw [←count_block,Nat.cast_add] at hc
  have hb : occupied (A+1)≤1 := by unfold occupied; split_ifs <;> norm_num
  have hn : 0≤occupied (A+H+1) := by unfold occupied; split_ifs <;> norm_num
  linarith only [hstart,hend,hsqrt,hc,hb,hn]

private def edgeSites (N : ℕ) := (range N).filter (fun k => 0<k ∧ Squarefree k ∧ Squarefree (k+1))

private theorem edge_nonempty {N : ℕ} (hN : 2≤N) : (edgeSites N).Nonempty := by
  refine ⟨1,mem_filter.mpr ⟨mem_range.mpr (by omega),by decide,?_⟩⟩
  exact ⟨squarefree_one,Nat.prime_two.squarefree⟩

/-- Largest lower endpoint of a squarefree neighbor pair below the cutoff. -/
def lastSquarefreeNeighbor (N : ℕ) :=
  if h : (edgeSites N).Nonempty then (edgeSites N).max' h else 0

private theorem last_mem {N : ℕ} (hN : 2≤N) : lastSquarefreeNeighbor N∈edgeSites N := by
  rw [lastSquarefreeNeighbor,dif_pos (edge_nonempty hN)]
  exact max'_mem _ _

private theorem le_last {N k : ℕ} (hk : k∈edgeSites N) : k≤lastSquarefreeNeighbor N := by
  rw [lastSquarefreeNeighbor,dif_pos ⟨k,hk⟩]
  exact le_max' _ _ hk

/-- The last squarefree neighbor is an occupied left endpoint and bounds every
other occupied left endpoint below the same cutoff. -/
theorem last_squarefree_neighbor_spec {N : ℕ} (hN : 2≤N) :
    let k := lastSquarefreeNeighbor N
    0<k ∧ k<N ∧ Squarefree k ∧ Squarefree (k+1) ∧
      ∀ j : ℕ,0 < j → j<N → Squarefree j → Squarefree (j+1) → j≤k := by
  obtain ⟨hr,hp,h₁,h₂⟩ := mem_filter.mp (last_mem hN)
  exact ⟨hp,mem_range.mp hr,h₁,h₂,fun j hj hjN h₃ h₄ =>
    le_last (mem_filter.mpr ⟨mem_range.mpr hjN,hj,h₃,h₄⟩)⟩

/-- The last occupied neighbor is within 80√N+6 of every cutoff.
No two-point Möbius cancellation estimate enters this bound. -/
theorem last_squarefree_neighbor_error {N : ℕ} (hN : 2≤N) :
    (N:ℝ)-lastSquarefreeNeighbor N≤80*Real.sqrt N+6 := by
  let k := lastSquarefreeNeighbor N
  let H := N-k-1
  have hm : k∈edgeSites N := last_mem hN
  obtain ⟨hkr,hpos,_,_⟩ := mem_filter.mp hm
  have hkN := mem_range.mp hkr
  have hcut : k+H+1=N := by dsimp only [H];omega
  have hvan : occupiedNeighbors k H=0 := by
    apply sum_eq_zero
    intro j hj
    have h₂ : ¬(Squarefree (k+j+1) ∧ Squarefree (k+j+2)) := by
      rintro ⟨h₁,h₂⟩
      have hj' := mem_range.mp hj
      have he : k+j+1∈edgeSites N := mem_filter.mpr
        ⟨mem_range.mpr (by omega),by omega,h₁,h₂⟩
      have hle : k+j+1≤k := le_last he
      omega
    by_cases h₁ : Squarefree (k+j+1)
    · have hn : ¬Squarefree (k+j+2) := fun ha => h₂ ⟨h₁,ha⟩
      simp [occupied,hn]
    · simp [occupied,h₁]
  have hc := squarefree_neighbor_count_lower hpos H
  rw [hvan] at hc
  have hd := mul_le_mul_of_nonneg_right density_margin.le (Nat.cast_nonneg H : 0≤(H:ℝ))
  have hs := Real.sqrt_le_sqrt (Nat.cast_le.mpr (show k+H≤N by omega) : ((k+H:ℕ):ℝ)≤N)
  have he : (k:ℝ)+(H:ℝ)+1=N := by exact_mod_cast hcut
  change (N:ℝ)-k≤_
  linarith only [he,hc,hd,hs]

open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open _root_.RHTower (mobiusRealCoefficient)

/-- The furthest occupied adjacent edge lies at asymptotically full length. -/
theorem last_squarefree_neighbor_ratio :
    Tendsto (fun N : ℕ => (lastSquarefreeNeighbor N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have hs := _root_.RHTower.tendsto_sqrt_natCast_div_natCast_atTop_zero
  have hi : Tendsto (fun N : ℕ => 6/(N:ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have he := (hs.const_mul 80).add hi
  simp only [mul_zero,add_zero] at he
  have hlow := (tendsto_const_nhds (x:=(1:ℝ))).sub he
  rw [sub_zero] at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
    have ht := (div_le_div_of_nonneg_right (last_squarefree_neighbor_error hN) hn.le)
    rw [sub_div,div_self hn.ne',add_div,mul_div_assoc] at ht
    linarith only [ht]
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hk := mem_range.mp (mem_filter.mp (last_mem hN)).1
    exact (div_le_one (Nat.cast_pos.mpr (by omega : 0<N) : 0<(N:ℝ))).mpr (Nat.cast_le.mpr hk.le)

private def mass (N : ℕ) := ∑ j∈Icc 1 N,mobiusRealCoefficient j^2/j

/-- Near every cutoff an actual squarefree edge forces the full window
energy to depart from its exact diagonal. The resolution cost N⁻²
is that of separating two reduced ratios in the finite spectrum. -/
theorem squarefree_window_departure {N : ℕ} (hN : 2≤N) :
    ∃ d : ℝ, (N:ℝ)⁻¹<d ∧ d≤1/(lastSquarefreeNeighbor N:ℝ)+((N:ℝ)^2)⁻¹ ∧
      bandEnergy N d≠d*∑ j∈Icc 1 N,mobiusRealCoefficient j^2/j := by
  let k := lastSquarefreeNeighbor N
  let x := adjacentLogGap k
  let h := ((N:ℝ)^2)⁻¹
  have hm : k∈edgeSites N := last_mem hN
  obtain ⟨hkr,hpos,h₁,h₂⟩ := mem_filter.mp hm
  have hkN := mem_range.mp hkr
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hp : 0<h := inv_pos.mpr (sq_pos_of_pos hn)
  have hcop : (k+1).Coprime k := by rw [Nat.add_comm k 1,Nat.coprime_add_self_left]; simp
  have hGram := (ratio_readout_ne_zero_iff (N:=N) (a:=k+1) (b:=k)
    (mem_Icc.mpr ⟨by omega,by omega⟩) (mem_Icc.mpr ⟨hpos,hkN.le⟩) hcop (by omega)
    hp le_rfl).mpr ⟨h₂,h₁⟩
  have hx := adjacent_log_gap_bounds hpos
  have hh : h≤x := by
    apply le_trans _ hx.1
    change ((N:ℝ)^2)⁻¹≤1/((k:ℝ)+1)
    rw [one_div]
    apply inv_anti₀ (by positivity)
    have hn1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
    have hk : (k:ℝ)+1≤N := by exact_mod_cast (show k+1≤N by omega)
    nlinarith only [hk,mul_nonneg hn.le (sub_nonneg.mpr hn1)]
  by_contra! hv
  have he (d : ℝ) (hd : 0≤d) (hwidth : d≤1/(k:ℝ)+h) : bandEnergy N d=d*mass N := by
    by_cases hb : d≤(N:ℝ)⁻¹
    · exact bandEnergy_diagonal hd hb
    · exact hv d (lt_of_not_ge hb) hwidth
  have hx0 := hp.le.trans hh
  have he₁ := he (x+h) (add_nonneg hx0 hp.le) (add_le_add hx.2 (le_refl h))
  have he₂ := he x hx0 (hx.2.trans (le_add_of_nonneg_right hp.le))
  have he₃ := he (x-h) (sub_nonneg.mpr hh) ((sub_le_self _ hp.le).trans
    (hx.2.trans (le_add_of_nonneg_right hp.le)))
  apply hGram
  change (bandEnergy N (x+h)-2*bandEnergy N x+bandEnergy N (x-h))/h=0
  rw [he₁,he₂,he₃]
  ring

/-- The constant one in the exact inverse-length diagonal band is
asymptotically optimal at every large cutoff, also with the actual Möbius signs. -/
theorem sharp_squarefree_diagonal_band (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∃ d : ℝ, (N:ℝ)⁻¹<d ∧ d<(1+ε)/(N:ℝ) ∧
      bandEnergy N d≠d*∑ j∈Icc 1 N,mobiusRealCoefficient j^2/j := by
  have hi := last_squarefree_neighbor_ratio.inv₀ one_ne_zero
  rw [inv_one] at hi
  have hninv : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hu := hi.add hninv
  rw [add_zero] at hu
  filter_upwards [eventually_ge_atTop 2,hu.eventually_lt_const (by linarith : 1<1+ε)] with N hN hnear
  obtain ⟨d,hd,hbound,hne⟩ := squarefree_window_departure hN
  refine ⟨d,hd,lt_of_le_of_lt hbound ?_,hne⟩
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hk : 0<(lastSquarefreeNeighbor N:ℝ) := Nat.cast_pos.mpr (mem_filter.mp (last_mem hN)).2.1
  apply (lt_div_iff₀ hn).mpr
  change ((lastSquarefreeNeighbor N:ℝ)/(N:ℝ))⁻¹+(N:ℝ)⁻¹<1+ε at hnear
  calc _ = ((lastSquarefreeNeighbor N:ℝ)/(N:ℝ))⁻¹+(N:ℝ)⁻¹ := by
           rw [inv_div]
           field_simp [hk.ne',hn.ne']
       _ < _ := hnear

#print axioms log_window_adjacent_band
#print axioms top_pair_in_full_window
#print axioms last_squarefree_neighbor_error
#print axioms squarefree_window_departure
#print axioms sharp_squarefree_diagonal_band
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
