import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.ScaledWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PolynomialFloor

/-! # Growing windows at prescribed delays before the phase-filling time -/
open Set MeasureTheory Filter Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
noncomputable section

def delayWindowWidth (N : ℕ) : ℝ := (N:ℝ)^((96:ℝ)⁻¹)

private theorem window_scales (m : ℕ) (A : ℝ) : ∀ᶠ k : ℕ in atTop,
    let N := k+3
    let w := delayWindowWidth N
    1 ≤ w ∧ A/(N:ℝ) ≤ 1 ∧ 16*((m:ℝ)*(8*w)) ≤ N ∧
      (m:ℝ)*(8*w)+2*w ≤ (N:ℝ)^((48:ℝ)⁻¹)/4 := by
  have hn : Tendsto (fun k : ℕ => ((k+3:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hw := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < (96:ℝ)⁻¹)).comp hn
  filter_upwards [hw.eventually_ge_atTop (16*(8*(m:ℝ)+2)),hn.eventually_ge_atTop A] with k hk hA
  intro N w
  change 16*(8*(m:ℝ)+2) ≤ w at hk
  change A ≤ (N:ℝ) at hA
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hw1 : 1 ≤ w := by linarith only [hk,Nat.cast_nonneg (α:=ℝ) m]
  have h0 := zero_le_one.trans hw1
  have hpow : w^2=(N:ℝ)^((48:ℝ)⁻¹) := by
    change ((N:ℝ)^((96:ℝ)⁻¹))^2=_
    rw [←Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    norm_num
  have hsq : w^2 ≤ N := by
    rw [hpow]
    exact (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (48:ℝ)⁻¹ ≤ 1)).trans_eq (Real.rpow_one _)
  have hmul := mul_le_mul_of_nonneg_right hk h0
  refine ⟨hw1,(div_le_one (zero_lt_one.trans_le hN)).mpr hA,?_,?_⟩
  · nlinarith only [hmul,hsq,h0]
  · rw [←hpow]
    nlinarith only [hmul,h0,mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) h0]

private theorem coordinate_card (k : ℕ) : (Fintype.card (PrefixIndex (k+1)):ℝ) ≤ 16*((k+3:ℕ):ℝ) := by
  rw [Fintype.card_congr (pathCoeffEquiv (k+1))]
  simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  push_cast
  linarith only [Nat.cast_nonneg (α:=ℝ) k]

/-- A grid spanning at most N/16 units has bounded Gaussian dilation
cost as soon as the observation delay exceeds N². -/
theorem grid_price {k m : ℕ} {g L : ℝ} (hg : 0 ≤ g) (hL : ((k+3:ℕ):ℝ)^2 ≤ L)
    (hm : 16*((m:ℝ)*g) ≤ ((k+3:ℕ):ℝ)) :
    (m:ℝ)*g ≤ L ∧ ∀ i : Fin m, 1 ≤ factor g L i ∧
      (Fintype.card (PrefixIndex (k+1)):ℝ)*(factor g L i-1) ≤ 1 := by
  let N := k+3
  have hN : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hl : 0 < L := (sq_pos_of_pos (zero_lt_one.trans_le hN)).trans_le hL
  have hmg := mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) hg
  have hspan : (m:ℝ)*g ≤ L := by
    have h : (m:ℝ)*g ≤ (N:ℝ) := by change 16*((m:ℝ)*g) ≤ (N:ℝ) at hm; linarith only [hm,hmg]
    exact h.trans ((le_self_pow₀ hN (by norm_num : 2 ≠ 0)).trans hL)
  refine ⟨hspan,fun i => ⟨(factor_bounds hg hl hspan i).1,?_⟩⟩
  have hi : (i.val:ℝ) ≤ m := by exact_mod_cast i.isLt.le
  have hmul := mul_le_mul (coordinate_card k) (mul_le_mul_of_nonneg_right hi hg)
    (mul_nonneg (Nat.cast_nonneg (α:=ℝ) i.val) hg) (by positivity)
  change _*(1+(i.val:ℝ)*g/L-1) ≤ 1
  rw [add_sub_cancel_left,←mul_div_assoc,div_le_one hl]
  apply hmul.trans
  apply le_trans _ hL
  have hprice := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α:=ℝ) (k+3))
  linarith only [hprice]

/-- A forbidden band for the difference of any two low-cost dates.
The estimate is simultaneous over both dates on a single draw. -/
theorem gaussian_distance_gap :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let s := ⌊c*sqrt N⌋₊
      ∀ t v : ℝ, pathGateDistance (k+1) s (prefixPoint k ω) t ≤ 1/10 →
        pathGateDistance (k+1) s (prefixPoint k ω) v ≤ 1/10 →
        A/(N:ℝ) ≤ |v-t| → |v-t| ≤ (N:ℝ)^((48:ℝ)⁻¹)/4 → False := by
  obtain ⟨A,c,hA,hc,hfloor⟩ := gaussian_pauli_polynomial_interval_cost_floor
  refine ⟨A,c/4,hA,by positivity,?_⟩
  filter_upwards [hfloor] with ω hf
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hf] with k hk
  intro N s
  let u := pathPauliDisorderShell ω (k+1)
  have hcost (v : ℝ) (h : pathGateDistance (k+1) s (prefixPoint k ω) v ≤ 1/10) :
      HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution (pathHamiltonian u) v) := by
    apply (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr
    rw [pathGateDistance,show numberedGenerator (k+1) (prefixPoint k ω)=pathHamiltonian u from numberedGenerator_shell u] at h
    exact h
  have hpos : 0 < sqrt (N:ℝ) := sqrt_pos.mpr (by dsimp [N]; positivity)
  have hcheap : (s:ℝ)+(s:ℝ) < c*sqrt N := by
    have h := Nat.floor_le (show 0 ≤ c/4*sqrt N by positivity)
    change (s:ℝ) ≤ _ at h
    linarith only [h,mul_pos hc hpos]
  have ordered (t v : ℝ) (ht : pathGateDistance _ s (prefixPoint k ω) t ≤ 1/10)
      (hv : pathGateDistance _ s (prefixPoint k ω) v ≤ 1/10)
      (hl : A/(N:ℝ) ≤ v-t) (hh : v-t ≤ (N:ℝ)^((48:ℝ)⁻¹)/4) : False := by
    have h := (hk (v-t) hl hh).2 t s s (hcost t ht)
    rw [show t+(v-t)=v by ring] at h
    exact hcheap.not_ge (h (hcost v hv))
  intro t v ht hv hl hh
  rcases le_total t v with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hl hh
    exact ordered t v ht hv hl hh
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr h)] at hl hh
    exact ordered v t hv ht hl hh

/-- For any preassigned delay L≥N², a window of length N^(1/96)
following the draw's first crossing has a vanishing probability of
even one physical visit with at most ⌊c√N⌋ gates. The crossing budget
may itself be any preassigned sequence. -/
theorem gaussian_prescribed_growing_window :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ → ℕ) (d : ℕ → ℝ),
      Tendsto (fun k => let N := k+3
                        let w := delayWindowWidth N
                        pathPauliDisorderLaw.real (prefixPoint k ⁻¹'
                          hitWindow (k+1) (P k) ⌊c*sqrt N⌋₊ (max (d k) ((N:ℝ)^2)) w)) atTop (𝓝 0) := by
  obtain ⟨A,c,hA,hc,hgap⟩ := gaussian_distance_gap
  refine ⟨c,hc,?_⟩
  intro P d
  let N (k : ℕ) := k+3
  let L (k : ℕ) := max (d k) (((N k):ℝ)^2)
  let w (k : ℕ) := delayWindowWidth (N k)
  let s (k : ℕ) := ⌊c*sqrt (N k)⌋₊
  let E (k : ℕ) := hitWindow (k+1) (P k) (s k) (L k) (w k)
  let a (m k : ℕ) := factor (m:=m) (8*w k) (L k)
  have hl (k : ℕ) : 0 < L k := (sq_pos_of_pos (show 0 < (N k:ℝ) by dsimp [N]; positivity)).trans_le (le_max_right ..)
  have hscale (m : ℕ) : ∀ᶠ k : ℕ in atTop,
      1 ≤ w k ∧ A/((N k):ℝ) ≤ 1 ∧ 16*((m:ℝ)*(8*w k)) ≤ N k ∧
        (m:ℝ)*(8*w k)+2*w k ≤ ((N k):ℝ)^((48:ℝ)⁻¹)/4 := window_scales m A
  apply prefix_probability_of_isolation E (fun _ => measurable_hitWindow ..) a
  · intro m
    filter_upwards [hscale m] with k h
    exact (grid_price (k:=k) (by linarith only [h.1]) (le_max_right ..) h.2.2.1).2
  · intro m
    filter_upwards [hgap] with ω hf
    filter_upwards [hf,hscale m] with k hk hs
    intro hx
    have hg : 0 ≤ 8*w k := by linarith only [hs.1]
    have hspan := (grid_price (k:=k) hg (le_max_right (d k) _) hs.2.2.1).1
    apply isolated_of_gap hg (hl k) hspan (zero_le_one.trans hs.1) _ hx
    intro t v ht hv hlo hhi
    exact hk t v ht hv (hs.2.1.trans (by linarith only [hlo,hs.1])) (hhi.trans hs.2.2.2)

#print axioms gaussian_prescribed_growing_window
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
