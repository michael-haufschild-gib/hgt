import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdDeficitAtTheEighthPowerEndpoints

/-!
# Parity of adjacent gcd horizon prices

At the sixteenth-power scale the error in replacing a Mangoldt octave by
its cofactor density is smaller than the spacing between adjacent density
levels. The density changes only after odd horizons. This gives the exact
leading term of a first difference even when successive prime octaves
are chosen independently. It distinguishes the local differences hidden
by the first-order, regularly varying shortfall.
-/

noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Signed shortfall at octave M and horizon mM. -/
def horizonShortfall (m M : ℕ) : ℝ :=
  Real.log 2 - Real.log (octaveGcdProduct M (m*M)) / ((m:ℝ)*M)

/-- Spacing of consecutive cofactor densities. -/
def oddHorizonSpacing (m : ℕ) : ℝ :=
  if m%2 = 0 then 0 else 1/((m:ℝ)*((m:ℝ)+1))

/-- The adjacent-density difference is exactly zero at even m and exactly
1/(m(m+1)) at odd m. -/
theorem adjacent_cofactor_density {m : ℕ} (hm : 1 ≤ m) :
    cofactorIntervalDensity (m+1) - cofactorIntervalDensity m = oddHorizonSpacing m := by
  rw [cofactor_density_harmonic (Nat.succ_pos m),cofactor_density_harmonic hm]
  let k := m/2
  have hk : m = 2*k ∨ m = 2*k+1 := by dsimp only [k]; omega
  rcases hk with he | ho
  · have hnext : (m+1)/2 = m/2 := by dsimp only [k] at he; omega
    rw [hnext,sub_self,oddHorizonSpacing,if_pos (by dsimp only [k] at he; omega)]
  · have hnext : (m+1)/2 = k+1 := by omega
    rw [hnext,oddHorizonSpacing,if_neg (by omega)]
    change ((harmonic (2*(k+1)):ℝ)-(harmonic (k+1):ℝ)) -
      ((harmonic (2*k):ℝ)-(harmonic k:ℝ)) = _
    rw [show 2*(k+1)=2*k+1+1 by omega]
    simp only [harmonic_succ,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
    have he : (m:ℝ) = 2*(k:ℝ)+1 := by exact_mod_cast ho
    rw [he]
    push_cast
    have h₀ : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
    field_simp <;> ring

/-- At every octave above the r-th power the density replacement gains
each exponent strictly below r times the zero-free width. -/
theorem horizon_density_precision {r : ℕ} (hr : 0 < r) {s : ℝ} (hs : 0 ≤ s)
    (hgap : s < (r:ℝ)*(1-_root_.RHTower.zeroReSup)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m M : ℕ}, 1 ≤ m → m^r ≤ M →
      |horizonShortfall m M - (Real.log 2 - cofactorIntervalDensity m)| ≤ C*(m:ℝ)^(-s) := by
  let t := 1-s/(r:ℝ)
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have ht : _root_.RHTower.zeroReSup < t := by
    have h := (div_lt_iff₀ hr').mpr (by simpa only [mul_comm (r:ℝ)] using hgap :
      s < (1-_root_.RHTower.zeroReSup)*(r:ℝ))
    dsimp only [t]; linarith only [h]
  obtain ⟨C,hC,h⟩ := gcd_product_density_above_zero_width ht
  refine ⟨C,hC,fun {m M} hm hM => ?_⟩
  have hm₀ : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hab := h ((one_le_pow₀ hm (n := r)).trans hM) hm
  have hpow := Real.rpow_le_rpow_of_nonpos (pow_pos hm₀ r)
    (show (m:ℝ)^r ≤ M by exact_mod_cast hM) (show t-1 ≤ 0 by
      dsimp only [t]; linarith only [div_nonneg hs hr'.le])
  rw [← Real.rpow_natCast (m:ℝ) r, ← Real.rpow_mul hm₀.le,
    show (r:ℝ)*(t-1) = -s by dsimp only [t]; field_simp; ring] at hpow
  have eqn : horizonShortfall m M-(Real.log 2-cofactorIntervalDensity m) =
      -(Real.log (octaveGcdProduct M (m*M))/((m:ℝ)*M)-cofactorIntervalDensity m) := by
    unfold horizonShortfall; ring
  rw [eqn,abs_neg]
  exact hab.trans (mul_le_mul_of_nonneg_left hpow hC)

private theorem precision_above_sixteenth_power :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m M : ℕ}, 1 ≤ m → m^16 ≤ M →
      |horizonShortfall m M - (Real.log 2 - cofactorIntervalDensity m)| ≤
        C*(m:ℝ)^(-2-1/3000:ℝ) := by
  rw [show (-2-1/3000:ℝ) = -(2+1/3000) by ring]
  apply horizon_density_precision (by decide) (by norm_num)
  norm_num only [Nat.cast_ofNat]
  linarith only [GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths]

/-- Across independently chosen octaves, the arithmetic shortfall has
the parity-dependent first difference with a uniform power-saving error. -/
theorem adjacent_gcd_horizons_with_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m M N : ℕ}, 1 ≤ m → m^16 ≤ M → (m+1)^16 ≤ N →
      |horizonShortfall m M - horizonShortfall (m+1) N - oddHorizonSpacing m| ≤
        C*(m:ℝ)^(-2-1/3000:ℝ) := by
  obtain ⟨C,hC,h⟩ := precision_above_sixteenth_power
  refine ⟨2*C,by positivity,fun {m M N} hm hM hN => ?_⟩
  have h₁ := h hm hM
  have h₂ := h (Nat.succ_pos m) hN
  have hr := Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hm : 0 < (m:ℝ))
    (Nat.cast_le.mpr (Nat.le_succ m)) (show (-2-1/3000:ℝ) ≤ 0 by norm_num)
  rw [←adjacent_cofactor_density hm]
  let e (i j : ℕ) := horizonShortfall i j - (Real.log 2-cofactorIntervalDensity i)
  calc _ = |e m M - e (m+1) N| := by congr 1; dsimp only [e]; ring
       _ ≤ |e m M| + |e (m+1) N| := abs_sub _ _
       _ ≤ _ := by
         have hh := h₂.trans (mul_le_mul_of_nonneg_left hr hC)
         dsimp only [e]
         linarith only [h₁,hh]

#print axioms horizon_density_precision
#print axioms adjacent_cofactor_density
#print axioms adjacent_gcd_horizons_with_remainder

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
