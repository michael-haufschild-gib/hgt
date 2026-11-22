import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Antipode
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.BinarySectors
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.NetworkHeat

/-!
# The heat carried by antipodal rejections

At maximal strict aperture a rejected label ratio brings all its
integer multiples. This forces the critical boundary on every nonempty
rejected sector. Adding it back restores the full square partition.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary

open SampledClocks CopyExchange
open scoped Classical

def rejected (t : ℝ) (x : Word) := ¬measured t Real.pi x

theorem rejected_iff (t : ℝ) (x : Word) :
    rejected t x ↔ ¬Survives Real.pi ((binary t).phase () x) := by
  have h := repeated_angles (binary t) (⟨Real.pi,Real.pi_pos.le,le_rfl⟩ : Set.Icc 0 Real.pi) x
  exact not_congr (h.trans ⟨fun h => h (),fun h _ => h⟩)

theorem rejected_difference (t : ℝ) : ∃ K : ℕ, ∀ x : Word,
    rejected t x ↔ (binary (((2^K:ℕ):ℝ)*t)).Resonant x ∧ ¬(binary t).Resonant x := by
  obtain ⟨K,hK⟩ := common_dyadic t
  refine ⟨K,fun x => ?_⟩
  rw [rejected_iff,misses_iff_return,hK x,binary_power]
  exact and_congr_right fun _ => not_congr ⟨fun h _ => h,fun h => h ()⟩

private theorem no_loss_zero (x : Word) : ¬rejected 0 x := by
  rw [rejected_iff,misses_iff_return]
  exact fun h => h.2 (by simp [Network.phase,binary])

private theorem ray_bound (t : ℝ) {s : ℂ} (hs : HasSectorHeat (rejected t) s)
    (x : Word) (hx : rejected t x) : 1/2 < s.re := by
  let along (n : ℕ+) : Word := fun b => n*x b
  have hphase (n : ℕ+) : (binary t).phase () (along n) = (binary t).phase () x := by
    change Circle.exp (t*(energy (n*x false)-energy (n*x true))) =
      Circle.exp (t*(energy (x false)-energy (x true)))
    rw [energy_mul,energy_mul,show energy n + energy (x false) - (energy n + energy (x true))
      = energy (x false) - energy (x true) by abel]
  let ray (n : ℕ+) : {w // rejected t w} := ⟨along n,(rejected_iff t _).mpr
    (by rw [hphase n]; exact (rejected_iff t x).mp hx)⟩
  have hi : Function.Injective ray := by
    intro n m he
    have h : n*x false = m*x false := congrArg (fun w : {w // rejected t w} => w.val false) he
    exact mul_right_cancel h
  let C := ‖wordHeat s x‖
  have hC : 0 < C := norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun b _ => Complex.exp_ne_zero _)
  have hsum := ((sectorHeat_iff _ _).mp hs).comp_injective (i := ray) hi
  have hrow : Summable (fun n : ℕ+ => C*‖heat s n‖^2) := by
    refine hsum.congr fun n => ?_
    change ‖wordHeat s (along n)‖ = _
    unfold C wordHeat
    simp only [Fintype.prod_bool,along,heat_mul,norm_mul]
    ring
  apply (summable_heat_sq_iff s).mp
  simpa only [← mul_assoc,inv_mul_cancel₀ hC.ne',one_mul] using hrow.mul_left C⁻¹

/-- A rejection is either absent altogether or already carries a critical-temperature ray. -/
theorem rejected_heat_iff (t : ℝ) (s : ℂ) : HasSectorHeat (rejected t) s ↔
    ((∃ x, rejected t x) → 1/2 < s.re) := by
  constructor
  · rintro h ⟨x,hx⟩
    exact ray_bound t h x hx
  · intro hs
    by_cases hex : ∃ x, rejected t x
    · have ht : t ≠ 0 := by rintro rfl; obtain ⟨x,h⟩ := hex; exact no_loss_zero x h
      have hper := (TorsionReadout.trace_iff t s).mpr (by rw [if_neg ht]; exact hs hex)
      apply restrict_heat _ _ hper
      intro x hx
      obtain ⟨k,hk⟩ := ((misses_iff_return _).mp ((rejected_iff t x).mp hx)).1
      exact ⟨⟨2^k,pow_pos (by norm_num) k⟩,hk⟩
    · letI : IsEmpty {x // rejected t x} := ⟨fun x => hex ⟨x.val,x.property⟩⟩
      exact (sectorHeat_iff _ _).mpr Summable.of_finite

/-- At the antipodal cutoff the accepted heat has the full-gas boundary at every time. -/
theorem maximal_heat_iff (t : ℝ) (s : ℂ) : HasSectorHeat (measured t Real.pi) s ↔ 1 < s.re := by
  constructor
  · intro h
    have hs : HasSectorHeat (binary t).Resonant s := by
      apply restrict_heat _ _ h
      intro x hx
      by_contra hn
      exact ((misses_iff_return _).mp ((rejected_iff t x).mp hn)).2 (hx ())
    have hb := (binary_threshold t s).mp hs
    have hh : 1/2 < s.re := by split at hb <;> linarith only [hb]
    exact (full_heat s).mp (join_heat _ s h ((rejected_heat_iff t s).mpr fun _ => hh))
  · exact fun h => restrict_heat _ (fun _ _ => trivial) ((full_heat s).mpr h)

def correction (t : ℝ) := partition (rejected t)

theorem maximal_trace (t : ℝ) (s : {z : ℂ // AbsoluteHeat (measured t Real.pi) z}) :
    ContinuousLinearMap.opTrace (sectorHeat (measured t Real.pi) s) = riemannZeta s.val^2-correction t s.val := by
  have h := (maximal_heat_iff t s.val).mp ((sectorHeat_iff _ _).mpr s.property)
  rw [operator_trace]
  exact eq_sub_of_add_eq (partition_complement (measured t Real.pi) ⟨s.val,h⟩)

#print axioms rejected_difference
#print axioms rejected_heat_iff
#print axioms maximal_heat_iff
#print axioms maximal_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary
