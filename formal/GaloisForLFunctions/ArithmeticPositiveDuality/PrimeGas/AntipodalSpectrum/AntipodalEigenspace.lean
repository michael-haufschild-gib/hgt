import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.OrderContrast

/-!
# The sector added by halving the sampling time

Doubling the time squares every phase. The words gained in passing from
time 2t to t are exactly the instantaneous antipodes. At the two calibrated
times their restricted heat operator realizes the scaled zeta divisor.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture DyadicAperture.Binary
open scoped Classical

def additional (t : ℝ) (x : Word) := rejected t x ∧ ¬rejected (2*t) x

private theorem double_phase (t : ℝ) (x : Word) :
    (binary (2*t)).phase () x = ((binary t).phase () x)^2 := by
  change Circle.exp ((2*t)*gap (x false) (x true)) = (Circle.exp (t*gap (x false) (x true)))^2
  rw [← Circle.exp_natCast_mul]
  congr 1
  push_cast
  ring

private theorem hit (t : ℝ) (x : Word) : rejected t x ↔ ∃ k : ℕ, ((binary t).phase () x)^(2^k : ℕ) = -1 :=
  (rejected_iff t x).trans (misses_pi _)

theorem rejected_nested (t : ℝ) (x : Word) : rejected (2*t) x → rejected t x := by
  rw [hit,hit,double_phase]
  rintro ⟨k,hk⟩
  exact ⟨k+1,by rwa [pow_succ',pow_mul]⟩

/-- The newly rejected words carry the eigenphase minus one on the first reading. -/
theorem additional_iff (t : ℝ) (x : Word) : additional t x ↔ (binary t).phase () x = -1 := by
  constructor
  · rintro ⟨h,hn⟩
    obtain ⟨k,hk⟩ := (hit t x).mp h
    cases k with
    | zero => simpa only [pow_zero,pow_one] using hk
    | succ k =>
      exact (hn ((hit _ _).mpr ⟨k,by rwa [double_phase,← pow_mul,← pow_succ']⟩)).elim
  · intro hp
    refine ⟨(hit t x).mpr ⟨0,by simpa only [pow_zero,pow_one] using hp⟩,?_⟩
    intro h
    have hn := ((misses_iff_return _).mp ((rejected_iff _ _).mp h)).2
    exact hn (by rw [double_phase,hp]; simp)

/-- The entire minus-one eigenspace of the physical unitary, including arbitrary waves. -/
theorem antipodal_eigenspace (t : ℝ) (f : LabelSpace Word) :
    (binary t).tick () f = -f ↔ f ∈ Sector (additional t) := by
  rw [sector_mem]
  constructor
  · intro h x hx
    by_contra hn
    apply hx
    apply (additional_iff t x).mpr
    have he := congrArg (fun v : LabelSpace Word => v x) h
    change ((binary t).phase () x : ℂ)*f x = -(f x) at he
    apply Subtype.ext
    exact mul_right_cancel₀ hn (he.trans (neg_one_mul (f x)).symm)
  · intro h
    apply lp.ext
    funext x
    change ((binary t).phase () x : ℂ)*f x = -(f x)
    by_cases hx : additional t x
    · rw [(additional_iff t x).mp hx]
      exact neg_one_mul _
    · rw [h x hx,mul_zero,neg_zero]

theorem additional_nonempty (t : ℝ) (h : 2*t ∈ exceptional) : ∃ x, additional t x := by
  obtain ⟨x,hx⟩ := h
  obtain ⟨k,hk⟩ := (hit _ _).mp hx
  let y (i : Bool) := (x i)^(2^(k+1) : ℕ)
  refine ⟨y,(additional_iff _ _).mpr (Eq.trans ?_ hk)⟩
  change Circle.exp (t*(energy ((x false)^_)-energy ((x true)^_))) =
    (Circle.exp ((2*t)*(energy (x false)-energy (x true))))^(2^k : ℕ)
  rw [← Circle.exp_natCast_mul]
  congr 1
  simp only [energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  ring

/-- Every nonempty additional sector has exactly the doubled radial heat boundary. -/
theorem additional_heat_iff (t : ℝ) (s : ℂ) :
    HasSectorHeat (additional t) s ↔ ((∃ x, additional t x) → 1/2 < s.re) := by
  constructor
  · rintro hs ⟨x,hx⟩
    let along (n : ℕ+) (i : Bool) := n*x i
    have hr (n : ℕ+) : additional t (along n) := by
      apply (additional_iff _ _).mpr
      rw [← (additional_iff _ _).mp hx]
      change Circle.exp (t*(energy (n*x false)-energy (n*x true))) = Circle.exp (t*(energy (x false)-energy (x true)))
      rw [energy_mul,energy_mul,show energy n+energy (x false)-(energy n+energy (x true)) = energy (x false)-energy (x true) by abel]
    let ray (n : ℕ+) : {w // additional t w} := ⟨along n,hr n⟩
    have hi : Function.Injective ray := fun n m he => mul_right_cancel (show n*x false = m*x false from
      congrArg (fun w : {w // additional t w} => w.val false) he)
    let C := ‖wordHeat s x‖
    have hC : C ≠ 0 := (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Complex.exp_ne_zero _) : 0 < C).ne'
    have hsum := ((sectorHeat_iff _ _).mp hs).comp_injective (i := ray) hi
    have hrow : Summable (fun n : ℕ+ => C*‖heat s n‖^2) := by
      refine hsum.congr fun n => ?_
      change ‖wordHeat s (along n)‖ = _
      simp only [C,wordHeat,Fintype.prod_bool,along,heat_mul,norm_mul]
      ring
    exact (summable_heat_sq_iff _).mp (by simpa only [← mul_assoc,inv_mul_cancel₀ hC,one_mul] using hrow.mul_left C⁻¹)
  · intro h
    by_cases he : ∃ x, additional t x
    · exact restrict_heat _ (fun _ hx => hx.1) ((rejected_heat_iff t s).mpr fun _ => h he)
    · letI : IsEmpty {x // additional t x} := ⟨fun x => he ⟨_,x.property⟩⟩
      exact (sectorHeat_iff _ _).mpr Summable.of_finite

theorem additional_partition_sum (t : ℝ) (s : {s : ℂ // 1/2 < s.re}) :
    correction (2*t) s.val + partition (additional t) s.val = correction t s.val := by
  let W := {x // rejected t x}
  let P (x : W) := rejected (2*t) x.val
  let e : {x : W // P x} ≃ {x // rejected (2*t) x} :=
    ⟨fun x => ⟨x.val.val,x.property⟩,fun x => ⟨⟨x.val,rejected_nested t _ x.property⟩,x.property⟩,fun _ => rfl,fun _ => rfl⟩
  let d : {x : W // ¬P x} ≃ {x // additional t x} :=
    ⟨fun x => ⟨x.val.val,x.val.property,x.property⟩,fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩,fun _ => rfl,fun _ => rfl⟩
  have hs := ((sectorHeat_iff _ _).mp ((rejected_heat_iff t s.val).mpr fun _ => s.property)).of_norm
  unfold correction partition
  rw [← e.tsum_eq,← d.tsum_eq]
  exact hs.tsum_subtype_add_tsum_subtype_compl {x : W | P x}

private theorem calibrated_double : halfTurnClock.val = 2*quarterTurnClock.val := by
  change 2*Real.pi/((2:ℝ)*energy 2) = 2*(2*Real.pi/((4:ℝ)*energy 2))
  have h : 0 < energy (2:ℕ+) := Real.log_pos (by norm_num)
  field_simp [h.ne']
  norm_num

theorem prime_additional_heat (s : ℂ) : HasSectorHeat (additional quarterTurnClock.val) s ↔ 1/2 < s.re := by
  rw [additional_heat_iff]
  exact ⟨fun h => h (additional_nonempty _ (calibrated_double ▸ halfTurnClock.property)),fun h _ => h⟩

/-- Operator trace on the antipodal eigenspace at the quarter-turn clock. -/
theorem prime_additional_trace (s : {z : ℂ // AbsoluteHeat (additional quarterTurnClock.val) z}) :
    ContinuousLinearMap.opTrace (sectorHeat (additional quarterTurnClock.val) s) =
      riemannZeta (2*s.val)*(2*(heat s.val 2)^2/(1-(heat s.val 2)^4)) := by
  have hβ := (prime_additional_heat _).mp ((sectorHeat_iff _ _).mpr s.property)
  have hs := additional_partition_sum quarterTurnClock.val ⟨s.val,hβ⟩
  change correction (2*quarterTurnClock.val) s.val + partition (additional quarterTurnClock.val) s.val =
    correction quarterTurnClock.val s.val at hs
  rw [← calibrated_double,response_eq_heat_sum halfTurnClock ⟨s.val,hβ⟩,response_eq_heat_sum quarterTurnClock ⟨s.val,hβ⟩] at hs
  rw [operator_trace,← prime_clock_difference ⟨s.val,by linarith only [hβ]⟩]
  linear_combination hs

/-- Continuation of the partition of the minus-one eigenspace at the quarter-turn time. -/
def antipodalPartition : ℂ → ℂ := response quarterTurnClock-response halfTurnClock

theorem antipodalPartition_meromorphic (s : ℂ) : MeromorphicAt antipodalPartition s :=
  (response_meromorphic quarterTurnClock s).sub (response_meromorphic halfTurnClock s)

theorem antipodalPartition_trace (s : {z : ℂ // AbsoluteHeat (additional quarterTurnClock.val) z}) :
    ContinuousLinearMap.opTrace (sectorHeat (additional quarterTurnClock.val) s) = antipodalPartition s.val := by
  have hβ := (prime_additional_heat _).mp ((sectorHeat_iff _ _).mpr s.property)
  exact (prime_additional_trace s).trans (prime_clock_difference ⟨s.val,by linarith only [hβ]⟩).symm

theorem antipodalPartition_divisor (s : {z : ℂ // 0 < z.re}) :
    meromorphicOrderAt antipodalPartition s.val = meromorphicOrderAt riemannZeta (2*s.val) := by
  obtain ⟨⟨hb,hm⟩,⟨hb',hm'⟩⟩ := prime_clock_parameters
  exact same_block_difference_order (hb'.trans hb.symm) (by rw [hm,hm']; norm_num) s

theorem rh_iff_antipodal_eigenspace_zeros_isometric : RiemannHypothesis ↔
    ∀ s : {s : ℂ // 0 < s.re ∧ s.re < 1/2}, antipodalPartition s.val = 0 →
      ∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split (2*s.val) f x := by
  rw [rh_iff_coincidence_isometric]
  apply forall_congr'
  intro s
  change ((∀ t u : ExceptionalTime, response t s.val = response u s.val) → _) ↔
    (response quarterTurnClock s.val-response halfTurnClock s.val = 0 → _)
  exact imp_congr ((universal_coincidence ⟨_,s.property.1⟩).trans
    ((prime_clock_coincidence ⟨_,s.property.1⟩).symm.trans sub_eq_zero.symm)) Iff.rfl

#print axioms rejected_nested
#print axioms additional_iff
#print axioms antipodal_eigenspace
#print axioms additional_nonempty
#print axioms additional_heat_iff
#print axioms prime_additional_heat
#print axioms prime_additional_trace
#print axioms antipodalPartition_trace
#print axioms antipodalPartition_meromorphic
#print axioms antipodalPartition_divisor
#print axioms rh_iff_antipodal_eigenspace_zeros_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
