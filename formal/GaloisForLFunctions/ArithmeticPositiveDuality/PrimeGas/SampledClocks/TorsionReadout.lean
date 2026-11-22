import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.ClockBoundary
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalPrimeFactorization

/-!
# A common return for every finite-order phase of the prime gas

An integer logarithmic relation between positive rationals holds in every
prime valuation. A single nonzero coordinate of a reference winding
bounds the denominators of all the rational windings at that time.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.TorsionReadout

open _root_.RHTower

private def IntegralAt (c : ℝ) (n : ℕ+) (q : ℚ) :=
  ∃ j : ℤ, (n.val:ℝ)*(c*Real.log (q:ℝ)) = j

private def PeriodicRatio (c : ℝ) (q : ℚ) := ∃ n : ℕ+, IntegralAt c n q

private theorem coordinate {q a : ℚ} (hq : 0 < q) (ha : 0 < a) (j k : ℤ)
    (h : (j:ℝ)*Real.log (q:ℝ) = (k:ℝ)*Real.log (a:ℝ)) (p : ℕ) :
    j*deningerRatExp q p = k*deningerRatExp a p := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have ha' : 0 < (a:ℝ) := by exact_mod_cast ha
  have he : (q:ℝ)^j = (a:ℝ)^k := Real.log_injOn_pos (zpow_pos hq' _) (zpow_pos ha' _)
    (by simpa only [Real.log_zpow] using h)
  have hr : q^j = a^k := by exact_mod_cast he
  have hv := congrArg (fun u : ℚ => deningerRatExp u p) hr
  simpa [deningerRatExp_zpow hq.ne',deningerRatExp_zpow ha.ne',zsmul_eq_mul] using hv

private theorem winding_coordinate {c : ℝ} (hc : c ≠ 0) {q a : ℚ} (hq : 0 < q) (ha : 0 < a)
    {n m : ℕ+} {j k : ℤ} (h : (n.val:ℝ)*(c*Real.log (q:ℝ)) = j)
    (h₀ : (m.val:ℝ)*(c*Real.log (a:ℝ)) = k) (p : ℕ) :
    ((n.val:ℤ)*k)*deningerRatExp q p = ((m.val:ℤ)*j)*deningerRatExp a p := by
  apply coordinate hq ha
  push_cast
  apply mul_left_cancel₀ hc
  calc
    _ = (k:ℝ)*((n.val:ℝ)*(c*Real.log (q:ℝ))) := by ring
    _ = (j:ℝ)*((m.val:ℝ)*(c*Real.log (a:ℝ))) := by rw [h,h₀,mul_comm]
    _ = _ := by ring

/-- All rational windings of a scaled logarithm of a positive rational have a common denominator. -/
private theorem common_denominator (c : ℝ) :
    ∃ N : ℕ+, ∀ q : ℚ, 0 < q → (PeriodicRatio c q ↔ IntegralAt c N q) := by
  classical
  by_cases hall : ∀ q : ℚ, 0 < q → PeriodicRatio c q → IntegralAt c 1 q
  · exact ⟨1,fun q hq => ⟨hall q hq,fun h => ⟨1,h⟩⟩⟩
  push Not at hall
  obtain ⟨a,ha,⟨m,k,h₀⟩,hn⟩ := hall
  have hc : c ≠ 0 := fun hz => hn ⟨0,by simp [hz]⟩
  have hane : a ≠ 1 := fun he => hn ⟨0,by simp [he]⟩
  have hex : ∃ p : ℕ, deningerRatExp a p ≠ 0 := by
    by_contra! hb
    exact hane ((deningerRatExp_eq_zero_iff ha).mp (Finsupp.ext fun p => hb p))
  obtain ⟨p,hp⟩ := hex
  let v := deningerRatExp a p
  let N : ℕ+ := ⟨m.val*v.natAbs^2,Nat.mul_pos m.pos (pow_pos (Int.natAbs_pos.mpr hp) _)⟩
  have hN : (N.val:ℝ) = (m.val:ℝ)*(v:ℝ)^2 := by
    have hs : (v.natAbs:ℤ)^2 = v^2 := by rw [Int.natCast_natAbs,sq_abs]
    have hs' : (v.natAbs:ℝ)^2 = (v:ℝ)^2 := by
      simpa only [Int.cast_pow,Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) hs
    change ((m.val*v.natAbs^2:ℕ):ℝ) = _
    rw [Nat.cast_mul,Nat.cast_pow,hs']
  refine ⟨N,fun q hq => ⟨?_,fun h => ⟨N,h⟩⟩⟩
  rintro ⟨n,j,hj⟩
  let u := deningerRatExp q p
  have hv : ((n.val:ℝ)*k)*(u:ℝ) = ((m.val:ℝ)*j)*(v:ℝ) := by
    exact_mod_cast winding_coordinate hc hq ha hj h₀ p
  refine ⟨k*u*v,?_⟩
  apply mul_left_cancel₀ (Nat.cast_pos.mpr n.pos : (0:ℝ) < n.val).ne'
  rw [hN]
  push_cast
  calc
    _ = (((m.val:ℝ)*((n.val:ℝ)*(c*Real.log (q:ℝ))))*v)*v := by ring
    _ = _ := by rw [hj,← hv]; ring

private def ratio (x : Bool → ℕ+) : ℚ := ((x false).val:ℚ)/(x true).val

private theorem ratio_pos (x : Bool → ℕ+) : 0 < ratio x :=
  div_pos (Nat.cast_pos.mpr (x false).pos) (Nat.cast_pos.mpr (x true).pos)

private theorem log_ratio (x : Bool → ℕ+) : Real.log (ratio x:ℝ) = energy (x false)-energy (x true) := by
  simp only [ratio,Rat.cast_div,Rat.cast_natCast,energy]
  exact Real.log_div (Nat.cast_pos.mpr (x false).pos).ne' (Nat.cast_pos.mpr (x true).pos).ne'

private theorem clock_winding (t : ℝ) (n : ℕ+) (x : Bool → ℕ+) :
    IntegralAt (t/(2*Real.pi)) n (ratio x) ↔ (binary ((n.val:ℝ)*t)).Resonant x := by
  have hphase : (binary ((n.val:ℝ)*t)).Resonant x ↔
      ∃ j : ℤ, ((n.val:ℝ)*t)*(energy (x false)-energy (x true)) = j*(2*Real.pi) :=
    ⟨fun h => Circle.exp_eq_one.mp (h ()),fun ⟨j,h⟩ _ => Circle.exp_eq_one.mpr ⟨j,h⟩⟩
  rw [hphase,IntegralAt,log_ratio]
  apply exists_congr
  intro j
  rw [show (n.val:ℝ)*(t/(2*Real.pi)*(energy (x false)-energy (x true))) =
    ((n.val:ℝ)*t)*(energy (x false)-energy (x true))/(2*Real.pi) by ring]
  exact div_eq_iff (mul_pos (by norm_num) Real.pi_pos).ne'

/-- The measured word returns after some positive number of ticks. -/
def periodic (t : ℝ) (x : Bool → ℕ+) : Prop :=
  ∃ n : ℕ+, ((binary t).phase () x)^n.val = 1

theorem periodic_iff (t : ℝ) (x : Bool → ℕ+) :
    periodic t x ↔ IsOfFinOrder ((binary t).phase () x) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  exact ⟨fun ⟨n,h⟩ => ⟨n.val,n.pos,h⟩,fun ⟨n,h,hp⟩ => ⟨⟨n,h⟩,hp⟩⟩

private theorem power_fixed (t : ℝ) (n : ℕ+) (x : Bool → ℕ+) :
    ((binary t).phase () x)^n.val = 1 ↔ (binary ((n.val:ℝ)*t)).Resonant x := by
  change (Circle.exp (t*(energy (x false)-energy (x true))))^n.val = 1 ↔
    ∀ _ : Unit, Circle.exp (((n.val:ℝ)*t)*(energy (x false)-energy (x true))) = 1
  rw [← Circle.exp_natCast_mul,mul_assoc]
  exact ⟨fun h _ => h,fun h => h ()⟩

/-- The entire periodic sector coincides with stationarity at a single integer multiple of the sampling time. -/
theorem common_return (t : ℝ) : ∃ N : ℕ+, periodic t = (binary ((N.val:ℝ)*t)).Resonant := by
  obtain ⟨N,hN⟩ := common_denominator (t/(2*Real.pi))
  refine ⟨N,funext fun x => propext ?_⟩
  rw [← clock_winding,← hN (ratio x) (ratio_pos x)]
  exact exists_congr fun n => (power_fixed t n x).trans (clock_winding t n x).symm

/-- All periodic occupations span the fixed space of a single sampled unitary. -/
theorem common_fixed (t : ℝ) : ∃ N : ℕ+, ∀ f : CopyExchange.LabelSpace (Bool → ℕ+),
    f ∈ Sector (periodic t) ↔ (binary ((N.val:ℝ)*t)).tick () f = f := by
  obtain ⟨N,hN⟩ := common_return t
  refine ⟨N,fun f => ?_⟩
  rw [hN,← Network.joint_fixed_iff]
  exact ⟨fun h => h (),fun h e => by cases e; exact h⟩

/-- Forgetting the return order preserves the sampled binary heat boundary. -/
theorem trace_iff (t : ℝ) (s : ℂ) : HasSectorHeat (periodic t) s ↔
    (if t = 0 then 1 else (1/2:ℝ)) < s.re := by
  obtain ⟨N,hN⟩ := common_return t
  rw [hN,binary_threshold]
  have hpos : (N.val:ℝ) ≠ 0 := (Nat.cast_pos.mpr N.pos).ne'
  simp [hpos]

#print axioms periodic_iff
#print axioms common_return
#print axioms common_fixed
#print axioms trace_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.TorsionReadout
