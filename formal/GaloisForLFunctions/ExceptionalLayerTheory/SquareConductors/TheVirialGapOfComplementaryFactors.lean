import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheVirialSymbolOnPrimePowerBlocks
import GaloisForLFunctions.HTGeometry.IntegerLogGap

/-!
# The continuum virial zero on complementary factors

For a factor d of k the frequency 6 log d / log k places the square
root of k at the neutral frequency 3 of the Kwak–Muñoz symbol.
At the continuum coupling 1/9 its value is exactly the squared
logarithmic difference of the complementary factors, with an explicit
positive weight. Distinct integer factors therefore leave a
gap on the scale 1/(k (log k)²).
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The square-root cut of a factor pair d,e has frequency three. -/
def factorFrequency (d e : ℕ) : ℝ := 6*Real.log d/Real.log ((d:ℝ)*e)

/-- Virial energy at the continuum threshold, multiplied by k (log k)². -/
def scaledFactorVirial (d e : ℕ) : ℝ :=
  ((d:ℝ)*e)*Real.log ((d:ℝ)*e)^2*blockVirialSymbol (1/9) (factorFrequency d e)

private theorem critical_square (x : ℝ) : blockVirialSymbol (1/9) x=(1+x)*(x-3)^2/9 := by
  unfold blockVirialSymbol
  ring

private theorem frequency_distance {d e : ℕ} (hd : 0<d) (he : 0<e) (hk : 1<d*e) :
    (factorFrequency d e-3)*Real.log ((d:ℝ)*e)=3*Real.log ((d:ℝ)/e) := by
  have dp : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have ep : 0<(e:ℝ) := Nat.cast_pos.mpr he
  have kp : 1<(d:ℝ)*e := by exact_mod_cast hk
  rw [factorFrequency,sub_mul,div_mul_cancel₀ _ (Real.log_pos kp).ne',Real.log_mul dp.ne' ep.ne',
    Real.log_div dp.ne' ep.ne']
  ring

/-- Exact scaled price of a factor pair under the critical virial symbol. -/
theorem factor_virial_identity {d e : ℕ} (hd : 0<d) (he : 0<e) (hk : 1<d*e) :
    scaledFactorVirial d e=(1+factorFrequency d e)*((d:ℝ)*e)*Real.log ((d:ℝ)/e)^2 := by
  have h := congrArg (fun t : ℝ => t^2) (frequency_distance hd he hk)
  rw [scaledFactorVirial,critical_square]
  linear_combination (1+factorFrequency d e)*((d:ℝ)*e)/9*h

/-- The squared integer gap, with the two possible endpoint ratios,
brackets the logarithmic cost. The bounds coincide asymptotically for
every fixed additive gap. -/
theorem factor_logarithmic_gap_sandwich {a b : ℕ} (ha : 0<a) (hab : a<b) :
    (a:ℝ)/b*((b:ℝ)-a)^2 ≤ ((a:ℝ)*b)*Real.log ((b:ℝ)/a)^2 ∧
      ((a:ℝ)*b)*Real.log ((b:ℝ)/a)^2 ≤ (b:ℝ)/a*((b:ℝ)-a)^2 := by
  have ap : 0<(a:ℝ) := Nat.cast_pos.mpr ha
  have bp : 0<(b:ℝ) := Nat.cast_pos.mpr (ha.trans hab)
  have diff : 0≤(b:ℝ)-a := sub_nonneg.mpr (Nat.cast_le.mpr hab.le)
  have low := GaloisForLFunctions.HTGeometry.gap_div_le_log_div ha hab
  have top : Real.log ((b:ℝ)/a)≤((b:ℝ)-a)/a := by
    rw [sub_div,div_self ap.ne']
    exact Real.log_le_sub_one_of_pos (div_pos bp ap)
  have pos := div_nonneg diff bp.le
  have below := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pos low 2) (mul_pos ap bp).le
  have above := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pos.trans low) top 2) (mul_pos ap bp).le
  refine ⟨le_trans ?_ below,above.trans ?_⟩ <;> apply le_of_eq <;> field_simp [ap.ne',bp.ne'] <;> ring

private theorem integer_gap_floor {a b : ℕ} (ha : 0<a) (hab : a<b) :
    (1/2:ℝ)≤((a:ℝ)*b)*Real.log ((b:ℝ)/a)^2 := by
  apply le_trans _ (factor_logarithmic_gap_sandwich ha hab).1
  let δ := (b:ℝ)-a
  have a1 : 1≤(a:ℝ) := Nat.one_le_cast.mpr ha
  have delta : 1≤δ := by
    have cast : (a:ℝ)+1≤b := by exact_mod_cast Nat.succ_le_of_lt hab
    dsimp only [δ]
    linarith only [cast]
  have bp : 0<(b:ℝ) := Nat.cast_pos.mpr (ha.trans hab)
  have small := le_mul_of_one_le_right (Nat.cast_nonneg (α:=ℝ) a) delta
  have gap := le_mul_of_one_le_left (zero_le_one.trans delta) a1
  have large := le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg (α:=ℝ) a) (zero_le_one.trans delta)) delta
  change 1/2≤(a:ℝ)/b*δ^2
  rw [show (a:ℝ)/b*δ^2=a*δ^2/b by ring,le_div_iff₀ bp]
  have add : (b:ℝ)=a+δ := by dsimp [δ]; ring
  linarith only [small,gap,large,add]

/-- Any unequal pair of positive factors has critical virial price at
least 1/(2k (log k)²), uniformly in the factorization. -/
theorem factor_virial_integer_floor {d e : ℕ} (hd : 0<d) (he : 0<e) (different : d≠e) :
    (1/2:ℝ)≤scaledFactorVirial d e := by
  have hk : 1<d*e := by
    rcases lt_or_gt_of_ne different with h|h
    · exact (show 1<e by omega).trans_le (Nat.le_mul_of_pos_left e hd)
    · exact (show 1<d by omega).trans_le (Nat.le_mul_of_pos_right d he)
  have core : (1/2:ℝ)≤((d:ℝ)*e)*Real.log ((d:ℝ)/e)^2 := by
    rcases lt_or_gt_of_ne different with h|h
    · rw [show (d:ℝ)/e=((e:ℝ)/d)⁻¹ by rw [inv_div],Real.log_inv,neg_sq]
      exact integer_gap_floor hd h
    · rw [mul_comm (d:ℝ) e]
      exact integer_gap_floor he h
  have kp : 1≤(d:ℝ)*e := by exact_mod_cast hk.le
  have freq : 0≤factorFrequency d e :=
    div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg d)) (Real.log_nonneg kp)
  rw [factor_virial_identity hd he hk,mul_assoc]
  exact core.trans (le_mul_of_one_le_left (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (sq_nonneg _)) (le_add_of_nonneg_right freq))

/-- Every nontrivial unitary factorization misses the continuum zero. -/
theorem unitary_factor_virial_floor {d e : ℕ} (cop : d.Coprime e) (hd : 0<d) (he : 0<e)
    (hk : 1<d*e) : (1/2:ℝ)≤scaledFactorVirial d e := by
  apply factor_virial_integer_floor hd he
  rintro rfl
  change d.gcd d=1 at cop
  rw [Nat.gcd_self] at cop
  simpa [cop] using hk

/-- Along every fixed positive integer gap h, the scaled virial
price converges to 4h². In particular adjacent, hence coprime, factors
attain finite limiting cost four at arbitrarily large conductors. -/
theorem fixed_factor_gap_virial_limit {h : ℕ} (hh : 0<h) :
    Tendsto (fun n : ℕ => scaledFactorVirial n (n+h)) atTop (𝓝 (4*(h:ℝ)^2)) := by
  let v (n : ℕ) : ℝ := (n+h:ℕ)
  have diff (n : ℕ) : v n-(n:ℝ)=h := by simp [v]
  have above (n : ℕ) : n<n+h := by omega
  have large {n : ℕ} (hn : 1≤n) : 1<n*(n+h) :=
    (show 1<n+h by omega).trans_le (Nat.le_mul_of_pos_left _ hn)
  have grow : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have prod : Tendsto (fun n : ℕ => (n:ℝ)*v n) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ grow
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact le_mul_of_one_le_right (Nat.cast_nonneg n) (Nat.one_le_cast.mpr (by omega : 1≤n+h))
  have ratio : Tendsto (fun n : ℕ => v n/n) atTop (𝓝 1) := by
    have lim : Tendsto (fun n : ℕ => 1+(h:ℝ)*(n:ℝ)⁻¹) atTop (𝓝 1) := by
      simpa only [mul_zero,add_zero] using ((grow.inv_tendsto_atTop.const_mul (h:ℝ)).const_add 1)
    apply lim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have np : 0<(n:ℝ) := Nat.cast_pos.mpr hn
    dsimp only [v]
    rw [Nat.cast_add,add_div,div_self np.ne',div_eq_mul_inv]
  have invratio : Tendsto (fun n : ℕ => (n:ℝ)/v n) atTop (𝓝 1) := by
    have lim := ratio.inv₀ one_ne_zero
    change Tendsto (fun n : ℕ => (v n/n)⁻¹) atTop (𝓝 (1:ℝ)⁻¹) at lim
    simpa only [inv_one,inv_div] using lim
  have core : Tendsto (fun n : ℕ => ((n:ℝ)*v n)*Real.log (v n/n)^2) atTop (𝓝 (h:ℝ)^2) := by
    have lo := invratio.mul_const ((h:ℝ)^2)
    have hi := ratio.mul_const ((h:ℝ)^2)
    rw [one_mul] at lo hi
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have g := (factor_logarithmic_gap_sandwich hn (above n)).1
      change (n:ℝ)/v n*(v n-n)^2≤_ at g
      rwa [diff] at g
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have g := (factor_logarithmic_gap_sandwich hn (above n)).2
      change _≤v n/(n:ℝ)*(v n-n)^2 at g
      rwa [diff] at g
  have reverse (n : ℕ) : Real.log ((n:ℝ)/v n) = -Real.log (v n/n) := by rw [←Real.log_inv,inv_div]
  have freq : Tendsto (fun n : ℕ => factorFrequency n (n+h)) atTop (𝓝 3) := by
    have logs : Tendsto (fun n : ℕ => Real.log (v n/n)) atTop (𝓝 0) := by
      simpa only [Real.log_one] using ratio.log one_ne_zero
    have invlog := (Real.tendsto_log_atTop.comp prod).inv_tendsto_atTop
    have lim : Tendsto (fun n : ℕ => 3-3*Real.log (v n/n)*(Real.log ((n:ℝ)*v n))⁻¹) atTop (𝓝 3) := by
      simpa only [Function.comp_def,mul_zero,zero_mul,sub_zero] using
        (tendsto_const_nhds (x:=(3:ℝ))).sub ((logs.const_mul 3).mul invlog)
    apply lim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have K : 1<(n:ℝ)*v n := by exact_mod_cast large hn
    have id := frequency_distance hn (hn.trans (above n).le) (large hn)
    change (factorFrequency n (n+h)-3)*Real.log ((n:ℝ)*v n)=3*Real.log ((n:ℝ)/v n) at id
    rw [reverse] at id
    have eq := (eq_div_iff (Real.log_pos K).ne').mpr id
    rw [div_eq_mul_inv] at eq
    linarith only [eq]
  have lim : Tendsto (fun n : ℕ => (1+factorFrequency n (n+h))*(((n:ℝ)*v n)*Real.log (v n/n)^2))
      atTop (𝓝 (4*(h:ℝ)^2)) := by
    simpa only [show 1+(3:ℝ)=4 by norm_num] using (freq.const_add 1).mul core
  apply lim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have price := factor_virial_identity hn (hn.trans (above n).le) (large hn)
  change scaledFactorVirial n (n+h)=(1+factorFrequency n (n+h))*((n:ℝ)*v n)*Real.log ((n:ℝ)/v n)^2 at price
  rw [reverse,neg_sq,mul_assoc] at price
  exact price.symm

#print axioms fixed_factor_gap_virial_limit
#print axioms factor_virial_identity
#print axioms factor_logarithmic_gap_sandwich
#print axioms factor_virial_integer_floor
#print axioms unitary_factor_virial_floor
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
