import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.CubicWindow
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.TorsionReadout

/-!
# Heat on networks of clocks with wide angular apertures

Each edge has one tick multiplier returning every periodic prime-gas
phase on that edge. Resampling preserves all active components.
The repeated-readout sector through 4π/5 lies between two stationary
sectors with identical heat domains.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture

open SampledClocks
open scoped Classical

private theorem torsion_of_cubic (z : Circle) (h : CubicAngle (angle z)) : IsOfFinOrder z := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rcases h with hz | ⟨k,hk⟩
  · have hu : z = 1 := by
      rcases representatives z with h | h <;> simpa [hz] using h
    exact ⟨1,by norm_num,by rw [hu,one_pow]⟩
  · let n := 3*2^k
    have hpos : 0 < n := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)
    have ht : (n:ℝ)*angle z = 2*Real.pi := by
      change ((3*2^k:ℕ):ℝ)*angle z = _
      rw [hk,cubic]
      push_cast
      field_simp
    refine ⟨n,hpos,?_⟩
    rcases representatives z with h | h
    · calc
        _ = (Circle.exp (angle z))^n := congrArg (fun w : Circle => w^n) h
        _ = 1 := by rw [← Circle.exp_natCast_mul,ht]; exact Circle.exp_eq_one.mpr ⟨1,by simp⟩
    · calc
        _ = (Circle.exp (-angle z))^n := congrArg (fun w : Circle => w^n) h
        _ = 1 := by rw [← Circle.exp_natCast_mul,mul_neg,ht]; exact Circle.exp_eq_one.mpr ⟨-1,by simp⟩

variable {I E : Type*}

/-- Each comparison may be repeated at its own positive whole number of ticks. -/
def resample (G : Network I E) (n : E → ℕ+) : Network I E :=
  ⟨G.src,G.dst,fun e => ((n e).val:ℝ)*G.time e⟩

def periodicWord (G : Network I E) (x : I → ℕ+) := ∀ e, IsOfFinOrder (G.phase e x)

/-- All edgewise periodic labels are stationary under a single choice of return times. -/
theorem periodic_resampling (G : Network I E) :
    ∃ n : E → ℕ+, periodicWord G = (resample G n).Resonant := by
  choose n hn using fun e => TorsionReadout.common_return (G.time e)
  refine ⟨n,funext fun x => propext ?_⟩
  apply forall_congr'
  intro e
  let word (b : Bool) := cond b (x (G.dst e)) (x (G.src e))
  change IsOfFinOrder ((binary (G.time e)).phase () word) ↔ _
  rw [← TorsionReadout.periodic_iff,hn e]
  exact ⟨fun h => h (),fun h _ => h⟩

private def edges (G : Network I E) (i j : I) :=
  ∃ e : G.Active, G.src e = i ∧ G.dst e = j

private theorem resample_edges (G : Network I E) (n : E → ℕ+) : edges (resample G n) = edges G := by
  funext i j
  apply propext
  constructor
  · rintro ⟨e,hs,hd⟩
    refine ⟨⟨e.val,fun hz => e.property ?_⟩,hs,hd⟩
    change ((n e.val).val:ℝ)*G.time e.val = 0
    rw [hz,mul_zero]
  · rintro ⟨e,hs,hd⟩
    exact ⟨⟨e.val,mul_ne_zero (Nat.cast_pos.mpr (n e.val).pos).ne' e.property⟩,hs,hd⟩

theorem resample_domain [Fintype I] (G : Network I E) (n : E → ℕ+) (s : ℂ) :
    (resample G n).Domain s ↔ G.Domain s := by
  let test (r : I → I → Prop) := ∀ c : Quot r, 1 < (Fintype.card {i : I // Quot.mk r i = c}:ℝ)*s.re
  change test (edges (resample G n)) ↔ test (edges G)
  rw [resample_edges]

/-- Even unrestricted finite return orders on the edges retain the exact network heat domain. -/
theorem periodic_heat_iff [Fintype I] [Fintype E] (G : Network I E) (s : ℂ) :
    HasSectorHeat (periodicWord G) s ↔ G.Domain s := by
  obtain ⟨n,h⟩ := periodic_resampling G
  rw [h,Network.traceClass_iff,resample_domain]

theorem repeated_angles (G : Network I E) (θ : Set.Icc 0 Real.pi) (x : I → ℕ+) :
    G.Repeated (Real.sqrt (aperture θ.val)) x ↔ ∀ e, Survives θ.val (G.phase e x) := by
  change (∀ k : ℕ, ∀ e, dist ((G.multiple (2^k)).phase e x) 1 < _) ↔ _
  simp only [Network.multiple_phase,chord_lt_iff θ]
  exact ⟨fun h e k => h k e,fun h k e => h e k⟩

theorem restrict_heat [Fintype I] {P Q : (I → ℕ+) → Prop} (s : ℂ)
    (inc : ∀ x, P x → Q x) (h : HasSectorHeat Q s) : HasSectorHeat P s := by
  let f (x : {x // P x}) : {x // Q x} := ⟨x.val,inc _ x.property⟩
  have hi : Function.Injective f := fun _ _ he => Subtype.ext (congrArg (fun y : {x // Q x} => y.val) he)
  exact (sectorHeat_iff _ _).mpr (((sectorHeat_iff _ _).mp h).comp_injective (i := f) hi)

/-- The entire finite network has its exact-clock heat domain at every strict aperture through 4π/5. -/
theorem wide_heat_iff [Fintype I] [Fintype E] (G : Network I E) (θ : Set.Ioc 0 fifth) (s : ℂ) :
    HasSectorHeat (G.Repeated (Real.sqrt (aperture θ.val))) s ↔ G.Domain s := by
  let u : Set.Icc 0 Real.pi := ⟨θ.val,θ.property.1.le,θ.property.2.trans (by unfold fifth; linarith only [Real.pi_pos])⟩
  constructor
  · intro h
    apply (G.traceClass_iff s).mp
    apply restrict_heat _ _ h
    intro x hx
    apply (repeated_angles G u x).mpr
    intro e k
    rw [hx e,one_pow]
    have hz : angle 1 = 0 := by simpa using exp_angle 0 ⟨le_rfl,Real.pi_pos.le⟩
    exact hz.trans_lt θ.property.1
  · intro h
    apply restrict_heat _ _ ((periodic_heat_iff G s).mpr h)
    intro x hx e
    exact torsion_of_cubic _ (necessary _ (fun k =>
      ((repeated_angles G u x).mp hx e k).trans_le θ.property.2))

theorem binary_heat_iff (t : ℝ) (θ : Set.Ioc 0 fifth) (s : ℂ) :
    HasSectorHeat ((binary t).Repeated (Real.sqrt (aperture θ.val))) s ↔
      (if t=0 then 1 else (1/2:ℝ)) < s.re :=
  (wide_heat_iff _ θ s).trans (((binary t).traceClass_iff s).symm.trans (binary_threshold t s))

/-- At nonzero time this measured heat boundary detects precisely the isometric splitting parameters. -/
theorem detects_split (t : {t : ℝ // t ≠ 0}) (θ : Set.Ioc 0 fifth) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ¬HasSectorHeat ((binary t.val).Repeated (Real.sqrt (aperture θ.val))) s ∧
        ∀ δ : ℝ, 0 < δ → HasSectorHeat ((binary t.val).Repeated (Real.sqrt (aperture θ.val))) (s+(δ:ℂ)) := by
  simpa only [binary_heat_iff,binary_threshold] using sampled_clock_split_iff t s

#print axioms periodic_resampling
#print axioms periodic_heat_iff
#print axioms repeated_angles
#print axioms wide_heat_iff
#print axioms binary_heat_iff
#print axioms detects_split

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture
