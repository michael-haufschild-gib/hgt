import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheTerminalOddQuotientHalfDetectsTheZeroAbscissa
import GaloisForLFunctions.PNTPlus.BrunTitchmarsh

/-!
# Square-root intervals of a large terminal prime discrepancy

Brun–Titchmarsh bounds the prime log mass on intervals of length Y by
O(Y) whenever the upper endpoint is at most Y³. It applies at both
ends of the terminal half. Either sign of the dyadic Chebyshev error
therefore stays above any square-root multiple throughout intervals
of any prescribed multiple of the square-root length.
-/

noncomputable section
open Filter Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private theorem uniform_short_prime_count :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℝ in atTop, ∀ a : ℝ, 0<a →
      (BrunTitchmarsh.primesBetween a (a+Y):ℝ)≤C*(Y/Real.log Y) := by
  obtain ⟨D,hD,err⟩ := BrunTitchmarsh.err_isBigO.exists_pos
  rw [Asymptotics.isBigOWith_iff] at err
  refine ⟨4+6*D,by positivity,?_⟩
  filter_upwards [err,eventually_gt_atTop (1:ℝ)] with Y bound hY
  intro a ha
  have yp := zero_lt_one.trans hY
  have lp := Real.log_pos hY
  have raw := BrunTitchmarsh.primesBetween_le a Y (Y^(1/2:ℝ)) ha yp
    (Real.one_lt_rpow hY (by norm_num))
  rw [Real.log_rpow yp] at raw
  have lead : 2*Y/((1/2:ℝ)*Real.log Y)=4*(Y/Real.log Y) := by
    field_simp [lp.ne']
    ring
  rw [lead] at raw
  change ‖Y^(1/2:ℝ)*(1+1/2*Real.log Y)^3‖≤D*‖Y/Real.log Y‖ at bound
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (div_pos yp lp)] at bound
  linarith only [raw,(le_abs_self _).trans bound]

/-- Uniform estimate for every subinterval of the sieve window.
The upper endpoint condition absorbs its individual prime log weights. -/
theorem linear_short_theta_error :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℝ in atTop, ∀ a b : ℕ, 0<a → a≤b → (b:ℝ)≤a+Y → (b:ℝ)≤Y^3 →
      |(Chebyshev.theta b-(b:ℝ))-(Chebyshev.theta a-(a:ℝ))|≤C*Y := by
  obtain ⟨C,hC,upper⟩ := uniform_short_prime_count
  refine ⟨3*C+1,by positivity,?_⟩
  filter_upwards [upper,eventually_gt_atTop (1:ℝ)] with Y cap late
  intro a b ha hab width size
  let S := (Ioc a b).filter Nat.Prime
  have ap : 0<(a:ℝ) := Nat.cast_pos.mpr ha
  have bp : 0<(b:ℝ) := Nat.cast_pos.mpr (ha.trans_le hab)
  have yp := zero_lt_one.trans late
  have lp := Real.log_pos late
  have inc : S⊆(Icc ⌈(a:ℝ)⌉₊ ⌊(a:ℝ)+Y⌋₊).filter Nat.Prime := by
    intro n h
    obtain ⟨row,pr⟩ := mem_filter.mp h
    obtain ⟨low,high⟩ := mem_Ioc.mp row
    rw [Nat.ceil_natCast]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨low.le,Nat.le_floor ((Nat.cast_le.mpr high).trans width)⟩,pr⟩
  have count : (S.card:ℝ)≤C*(Y/Real.log Y) :=
    (Nat.cast_le.mpr (card_le_card inc)).trans (cap a ap)
  have logs : Real.log b≤3*Real.log Y := by simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log bp size
  have raw : (∑ n ∈ S,Real.log n)≤∑ _ ∈ S,3*Real.log Y := by
    apply sum_le_sum
    intro n hn
    have h := mem_filter.mp hn
    exact (Real.log_le_log (Nat.cast_pos.mpr h.2.pos) (Nat.cast_le.mpr (mem_Ioc.mp h.1).2)).trans logs
  rw [sum_const,nsmul_eq_mul] at raw
  have theta := _root_.RHTower.theta_window_eq hab
  change Chebyshev.theta b-Chebyshev.theta a=∑ n ∈ S,Real.log n at theta
  have afford : C*(Y/Real.log Y)*(3*Real.log Y)=3*C*Y := by field_simp [lp.ne']
  have paid := raw.trans ((mul_le_mul_of_nonneg_right count (by positivity : 0≤3*Real.log Y)).trans_eq afford)
  have mono := Chebyshev.theta_mono (Nat.cast_le.mpr hab : (a:ℝ)≤b)
  apply abs_le.mpr
  constructor <;> linarith only [theta,paid,mono,width,(Nat.cast_le.mpr hab : (a:ℝ)≤b),yp,mul_pos hC yp]

private theorem sqrt_grows : Tendsto (fun X : ℕ => Real.sqrt X) atTop atTop := by
  simpa only [Function.comp_def,Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))

/-- A single linear movement estimate holds simultaneously at all
widths Y above √X, including widths chosen separately for each X. -/
theorem terminal_half_uniform_window :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ Y : ℝ, Real.sqrt X≤Y → ∀ H : ℕ,
      X≤H → (H:ℝ)≤X+Y → |terminalOddHalf H-terminalOddHalf X|≤C*Y := by
  obtain ⟨C,hC,cap⟩ := linear_short_theta_error
  obtain ⟨Y₀,hY₀⟩ := eventually_atTop.mp cap
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [sqrt_grows.eventually_ge_atTop (max Y₀ 2),eventually_ge_atTop 4] with X late hX
  intro Y window H lo high
  have sieve := hY₀ Y ((le_max_left Y₀ 2).trans (late.trans window))
  have two : 2≤Y := (le_max_right Y₀ 2).trans (late.trans window)
  have square := Real.sq_sqrt (Nat.cast_nonneg X : 0≤(X:ℝ))
  have sqcap := pow_le_pow_left₀ (Real.sqrt_nonneg (X:ℝ)) window 2
  rw [square] at sqcap
  have top : (H:ℝ)≤Y^3 := by
    have yp : 0≤Y := (by norm_num : (0:ℝ)≤2).trans two
    have one : 1≤Y := (by norm_num : (1:ℝ)≤2).trans two
    linarith only [high,sqcap,mul_le_mul_of_nonneg_right one yp,mul_le_mul_of_nonneg_right two (sq_nonneg Y)]
  have halves : X/2≤H/2 := by omega
  have width : (↑(H/2):ℝ)≤(↑(X/2):ℝ)+Y := by
    have nat : H/2+X≤X/2+H := by omega
    have cast : (↑(H/2):ℝ)+X≤(↑(X/2):ℝ)+H := by exact_mod_cast nat
    linarith only [cast,high]
  have q₁ := sieve X H (by omega) lo high top
  have q₂ := sieve (X/2) (H/2) (by omega) halves width ((Nat.cast_le.mpr (Nat.div_le_self H 2)).trans top)
  let E (n : ℕ) := Chebyshev.theta n-(n:ℝ)
  have diff : terminalOddHalf H-terminalOddHalf X=(E H-E X)-(E (H/2)-E (X/2)) := by
    rw [terminal_odd_half_eq,terminal_odd_half_eq]
    dsimp only [E]
    ring
  rw [diff]
  apply (abs_sub ..).trans
  change |E H-E X|≤C*Y at q₁
  change |E (H/2)-E (X/2)|≤C*Y at q₂
  change |E H-E X|+|E (H/2)-E (X/2)|≤2*C*Y
  linarith only [q₁,q₂]

/-- The movement over any fixed multiple of the square-root length
is linear in that multiple, with an absolute constant. -/
theorem terminal_half_root_movement :
    ∃ C : ℝ, 0<C ∧ ∀ R : ℝ, 1≤R → ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
      X≤H → (H:ℝ)≤X+R*Real.sqrt X →
      |terminalOddHalf H-terminalOddHalf X|≤C*(R*Real.sqrt X) := by
  obtain ⟨C,hC,cap⟩ := terminal_half_uniform_window
  exact ⟨C,hC,fun R hR => cap.mono (fun X h => h _ (le_mul_of_one_le_left (Real.sqrt_nonneg _) hR))⟩

/-- For either prescribed orientation the same square-root excursion
persists throughout arbitrarily long fixed multiples of √X. -/
theorem terminal_half_long_root_excursions {s : ℝ} (hs : s=1 ∨ s= -1) (R A : ℝ) (hR : 1≤R) (hA : 0≤A) :
    ∃ᶠ X : ℕ in atTop, ∀ H : ℕ, X≤H → (H:ℝ)≤X+R*Real.sqrt X → A*Real.sqrt X<s*terminalOddHalf H := by
  obtain ⟨C,hC,cap⟩ := terminal_half_root_movement
  have sg : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
  apply ((terminal_odd_half_sqrt_excursions hs (A+C*R)
    (add_nonneg hA (mul_nonneg hC.le (zero_le_one.trans hR)))).and_eventually (cap R hR)).mono
  rintro X ⟨big,move⟩ H lo hi
  have swing := le_abs_self (s*(terminalOddHalf X-terminalOddHalf H))
  rw [abs_mul,sg,one_mul,abs_sub_comm (terminalOddHalf X) (terminalOddHalf H)] at swing
  linarith only [big,swing,move H lo hi]

#print axioms linear_short_theta_error
#print axioms terminal_half_uniform_window
#print axioms terminal_half_root_movement
#print axioms terminal_half_long_root_excursions
end GaloisForLFunctions.ExclusionOfTheCriticalState
