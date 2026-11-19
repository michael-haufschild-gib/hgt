import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheParityOfAdjacentGcdHorizonPrices

/-!
# Fourth order of the even-horizon shortfall

Subtracting the first two reciprocal powers from the shortfall at even m
leaves an exact positive rational difference on each pair of cells.
Telescoping between two shifted fourth powers gives sharp endpoint bounds.
The arithmetic error at octaves above the thirty-second power is small
enough to preserve the fourth coefficient.
-/

noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def evenIndex (k : ℕ) := 2*(k+1)
private def correction (x : ℝ) := 1/(2*x)-1/(4*x^2)
private def fourth (x : ℝ) := 1/(8*x^4)
private def remainder (k : ℕ) :=
  Real.log 2-cofactorIntervalDensity (evenIndex k)-correction (evenIndex k)

private theorem even_top : Tendsto evenIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  dsimp only [evenIndex]; omega

private theorem even_succ (k : ℕ) : evenIndex (k+1) = evenIndex k+2 := by
  dsimp only [evenIndex]; omega

private theorem remainder_zero : Tendsto remainder atTop (𝓝 0) := by
  have h := (Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)).sub
    (Real.tendsto_harmonic_sub_log.comp even_top)
  rw [sub_self] at h
  have hc : Tendsto (fun k => Real.log 2-cofactorIntervalDensity (evenIndex k)) atTop (𝓝 0) := by
    apply h.congr
    intro k
    have hpos : 0 < evenIndex k := by dsimp only [evenIndex]; omega
    rw [cofactor_density_harmonic hpos,show evenIndex k / 2 = k+1 by dsimp only [evenIndex]; omega]
    change ((harmonic (k+1):ℝ)-Real.log (k+1:ℕ))-
      ((harmonic (evenIndex k):ℝ)-Real.log (evenIndex k)) = _
    simp only [evenIndex,Nat.cast_mul,Nat.cast_ofNat, Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
      (Nat.cast_pos.mpr (Nat.succ_pos k) : 0 < ((k+1:ℕ):ℝ)).ne']
    ring
  have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp even_top
  have h₁ : Tendsto (fun k => 1/(2*(evenIndex k:ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (ht.const_mul_atTop (by norm_num))
  have h₂ : Tendsto (fun k => 1/(4*(evenIndex k:ℝ)^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp ht).const_mul_atTop
      (by norm_num))
  simpa only [remainder,correction,sub_zero] using hc.sub (h₁.sub h₂)

private theorem remainder_difference (k : ℕ) :
    remainder k - remainder (k+1) =
      1/((evenIndex k:ℝ)^2*((evenIndex k:ℝ)+1)*((evenIndex k:ℝ)+2)^2) := by
  let m := evenIndex k
  have hm : 1 ≤ m := by dsimp only [m,evenIndex]; omega
  have he := adjacent_cofactor_density hm
  have ho := adjacent_cofactor_density (m:=m+1) (by omega)
  rw [oddHorizonSpacing,if_pos (by dsimp only [m,evenIndex]; omega)] at he
  rw [oddHorizonSpacing,if_neg (by dsimp only [m,evenIndex]; omega),Nat.cast_succ] at ho
  have hstep : cofactorIntervalDensity (m+2)-cofactorIntervalDensity m =
      1/(((m:ℝ)+1)*((m:ℝ)+2)) := by
    rw [show (m:ℝ)+2 = ((m:ℝ)+1)+1 by ring]
    linarith only [he,ho]
  dsimp only [remainder]
  rw [even_succ,Nat.cast_add,Nat.cast_ofNat]
  change (Real.log 2-cofactorIntervalDensity m-correction m)-
    (Real.log 2-cofactorIntervalDensity (m+2)-correction ((m:ℝ)+2))=_
  rw [show (Real.log 2-cofactorIntervalDensity m-correction m)-
      (Real.log 2-cofactorIntervalDensity (m+2)-correction ((m:ℝ)+2)) =
      (cofactorIntervalDensity (m+2)-cofactorIntervalDensity m)-(correction m-correction ((m:ℝ)+2)) by ring,
    hstep]
  have hpos : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  change _ = 1/((m:ℝ)^2*((m:ℝ)+1)*((m:ℝ)+2)^2)
  dsimp only [correction]
  field_simp
  ring

private theorem fourth_brackets {x : ℝ} (hx : 0 < x) :
    fourth (x+2)-fourth (x+4) ≤ 1/(x^2*(x+1)*(x+2)^2) ∧
    1/(x^2*(x+1)*(x+2)^2) ≤ fourth x-fourth (x+2) := by
  constructor <;> dsimp only [fourth] <;> field_simp <;>
    apply sub_nonneg.mp <;> ring_nf <;> positivity

/-- Even cofactor densities have a positive fourth-order remainder between
two explicit translates. In particular the third-order coefficient vanishes. -/
theorem even_cofactor_fourth_bracket (k : ℕ) :
    let m : ℝ := 2*((k:ℝ)+1)
    let e := Real.log 2-cofactorIntervalDensity (2*(k+1))-(1/(2*m)-1/(4*m^2))
    1/(8*(m+2)^4) ≤ e ∧ e ≤ 1/(8*m^4) := by
  have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp even_top
  have hfour {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
      Tendsto (fun i => fourth (f i)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (((tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0)).comp hf).const_mul_atTop
      (by norm_num))
  let low := fun i : ℕ => remainder i-fourth ((evenIndex i:ℝ)+2)
  let up := fun i : ℕ => remainder i-fourth (evenIndex i)
  have hl : Antitone low := by
    apply antitone_nat_of_succ_le
    intro i
    have he := remainder_difference i
    have hx : 0 < (evenIndex i:ℝ) := by dsimp only [evenIndex]; positivity
    have hb := (fourth_brackets hx).1
    dsimp only [low]
    rw [even_succ,Nat.cast_add,Nat.cast_ofNat,show (evenIndex i:ℝ)+2+2 = (evenIndex i:ℝ)+4 by ring]
    linarith only [he,hb]
  have hu : Monotone up := by
    apply monotone_nat_of_le_succ
    intro i
    have he := remainder_difference i
    have hx : 0 < (evenIndex i:ℝ) := by dsimp only [evenIndex]; positivity
    have hb := (fourth_brackets hx).2
    dsimp only [up]
    rw [even_succ,Nat.cast_add,Nat.cast_ofNat]
    linarith only [he,hb]
  have hL : Tendsto low atTop (𝓝 0) := by
    simpa only [sub_zero] using remainder_zero.sub (hfour (tendsto_atTop_add_const_right _ 2 ht))
  have hU : Tendsto up atTop (𝓝 0) := by
    simpa only [sub_zero] using remainder_zero.sub (hfour ht)
  have h := And.intro (sub_nonneg.mp (hl.le_of_tendsto hL k)) (sub_nonpos.mp (hu.ge_of_tendsto hU k))
  simpa only [fourth,remainder,correction,evenIndex,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_succ] using h

/-- The fourth coefficient is 1/8 in the actual gcd shortfall at every
choice of even horizons whose octaves begin above the thirty-second power. -/
theorem even_gcd_fourth_coefficient (M : ℕ → ℕ)
    (hM : ∀ᶠ k : ℕ in atTop, (2*(k+1))^32 ≤ M k) :
    Tendsto (fun k : ℕ => let m := 2*(k+1)
      (m:ℝ)^4*(horizonShortfall m (M k)-(1/(2*(m:ℝ))-1/(4*(m:ℝ)^2)))) atTop (𝓝 (1/8)) := by
  have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp even_top
  have hquot : Tendsto (fun k => (evenIndex k:ℝ)/((evenIndex k:ℝ)+2)) atTop (𝓝 1) := by
    have hsmall : Tendsto (fun k => 2/((evenIndex k:ℝ)+2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 ht)
    have h := (tendsto_const_nhds (x:=(1:ℝ))).sub hsmall
    rw [sub_zero] at h
    exact h.congr fun i => by
      change 1-2/((evenIndex i:ℝ)+2) = _
      have hp : 0 < (evenIndex i:ℝ)+2 := by positivity
      field_simp
      ring
  have hbase : Tendsto (fun k => (evenIndex k:ℝ)^4*remainder k) atTop (𝓝 (1/8)) := by
    have hlo := (hquot.pow 4).div_const 8
    rw [one_pow] at hlo
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    all_goals
      filter_upwards with k
      have hm : 0 < (evenIndex k:ℝ) := by dsimp only [evenIndex]; positivity
      have h := even_cofactor_fourth_bracket k
      have he : 2*((k:ℝ)+1) = (evenIndex k:ℝ) := by simp [evenIndex]
      dsimp only at h
      rw [he] at h
    · have hh := mul_le_mul_of_nonneg_left h.1 (pow_nonneg hm.le 4)
      change _ ≤ (evenIndex k:ℝ)^4*remainder k
      refine le_trans ?_ hh
      rw [div_pow]
      exact (by ring : _ = _).le
    · have hh := mul_le_mul_of_nonneg_left h.2 (pow_nonneg hm.le 4)
      exact hh.trans_eq (by field_simp)
  obtain ⟨C,hC,h⟩ := horizon_density_precision (r:=32) (s:=4+1/3000) (by norm_num) (by norm_num) (by
    norm_num only [Nat.cast_ofNat]
    linarith only [GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths])
  let err := fun k => (evenIndex k:ℝ)^4*(horizonShortfall (evenIndex k) (M k)-
    (Real.log 2-cofactorIntervalDensity (evenIndex k)))
  have hsmall : Tendsto (fun k => C*(evenIndex k:ℝ)^(-(1/3000):ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1/3000:ℝ))).comp ht).const_mul C
  have he : Tendsto err atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hsmall
    filter_upwards [hM] with k hk
    have hp : 0 < (evenIndex k:ℝ) := by dsimp only [evenIndex]; positivity
    have hh := mul_le_mul_of_nonneg_left (h (m:=evenIndex k) (by dsimp only [evenIndex]; omega) hk)
      (pow_nonneg hp.le 4)
    rw [mul_left_comm _ C,←Real.rpow_natCast (evenIndex k:ℝ) 4,←Real.rpow_add hp,
      show ((4:ℕ):ℝ) + -(4+1/3000:ℝ) = -(1/3000:ℝ) by norm_num] at hh
    simpa only [err,Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hp.le 4)] using hh
  have hall := he.add hbase
  rw [zero_add] at hall
  exact hall.congr fun k => by dsimp only [err,remainder,correction,evenIndex]; ring

#print axioms even_cofactor_fourth_bracket
#print axioms even_gcd_fourth_coefficient

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
