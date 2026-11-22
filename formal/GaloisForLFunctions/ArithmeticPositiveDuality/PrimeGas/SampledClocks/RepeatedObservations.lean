import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.Precision
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.DyadicPhase

/-!
# Finite and unlimited dyadic observations

Every finite list of positive-radius comparisons retains the full-gas
threshold. The same test at all dyadic multiples recovers the exact
sampled sector at any strict radius up to the square root of three.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

open CopyExchange
open scoped Classical

variable {I E : Type*}

namespace Network

variable (G : Network I E)

/-- Multiply every clock time by the same natural number. -/
def multiple (n : ℕ) : Network I E := ⟨G.src,G.dst,fun e => (n : ℝ)*G.time e⟩

theorem multiple_phase (n : ℕ) (e : E) (x : I → ℕ+) : (G.multiple n).phase e x = (G.phase e x)^n := by
  unfold multiple phase
  rw [mul_assoc,Circle.exp_natCast_mul]

def Prefix (r : ℝ) (N : ℕ) (x : I → ℕ+) : Prop :=
  ∀ k : Fin N, ∀ e, dist ((G.multiple (2^(k : ℕ))).phase e x) 1 < r

def Repeated (r : ℝ) (x : I → ℕ+) : Prop := ∀ k : ℕ, ∀ e, dist ((G.multiple (2^k)).phase e x) 1 < r

theorem resonant_prefix (r : {r : ℝ // 0 < r}) (N : ℕ) (x : I → ℕ+) (h : G.Resonant x) : G.Prefix r.val N x := by
  intro k e
  simpa only [G.multiple_phase,h e,one_pow,dist_self] using r.property

theorem repeated_eq (r : {r : ℝ // 0 < r}) (hr : r.val ≤ Real.sqrt 3) : G.Repeated r.val = G.Resonant := by
  funext x
  apply propext
  change (∀ k : ℕ, ∀ e : E, dist ((G.multiple (2^k)).phase e x) 1 < r.val) ↔ ∀ e, G.phase e x = 1
  simp only [multiple_phase]
  constructor
  · intro h e
    exact ((dyadic_radius_iff r).mpr hr (G.phase e x)).mp fun k => h k e
  · intro h k e
    simpa only [h e,one_pow,dist_self] using r.property

private def unobserved (I : Type*) : Network I Empty := ⟨Empty.elim,Empty.elim,Empty.elim⟩

private def prefixReadout (r : {r : ℝ // 0 < r}) (N : ℕ) : Readout I (Fin N × E) (fun _ => Circle) where
  left j := G.src j.2
  right j := G.dst j.2
  value j := clockPhase (((2^j.1.val : ℕ) : ℝ)*G.time j.2)
  radius _ := r

private theorem prefix_accepted (r : {r : ℝ // 0 < r}) (N : ℕ) :
    G.Prefix r.val N = Accepted (unobserved I) (G.prefixReadout r N) := by
  funext x
  apply propext
  constructor
  · intro h
    refine ⟨fun e => e.elim,?_⟩
    rintro ⟨k,e⟩
    have he := h k e
    rw [(G.multiple (2^k.val)).phase_distance] at he
    exact he
  · rintro ⟨_,h⟩ k e
    rw [(G.multiple (2^k.val)).phase_distance]
    exact h (k,e)

/-- Every finite prefix of positive-radius observations has trace-class boundary one. -/
theorem prefix_heat_iff [Fintype I] [Nonempty I] [Fintype E] (r : {r : ℝ // 0 < r}) (N : ℕ) (s : ℂ) :
    HasSectorHeat (G.Prefix r.val N) s ↔ 1 < s.re := by
  rw [G.prefix_accepted,accepted_heat_iff]
  have hc (c : (unobserved I).Component) : (unobserved I).size c = 1 := (unobserved I).size_of_no_active c
  constructor
  · intro h
    simpa only [hc,Nat.cast_one,one_mul] using h ((unobserved I).component (Classical.arbitrary I))
  · intro h c
    simpa only [hc,Nat.cast_one,one_mul] using h

theorem repeated_heat_iff [Fintype I] [Fintype E] (r : {r : ℝ // 0 < r}) (hr : r.val ≤ Real.sqrt 3) (s : ℂ) :
    HasSectorHeat (G.Repeated r.val) s ↔ G.Domain s := by rw [G.repeated_eq r hr,G.traceClass_iff]

/-- Each coordinate eventually receives its exact acceptance decision. -/
theorem prefix_eventually (r : {r : ℝ // 0 < r}) (hr : r.val ≤ Real.sqrt 3) (x : I → ℕ+) :
    ∀ᶠ N : ℕ in Filter.atTop, G.Prefix r.val N x ↔ G.Resonant x := by
  by_cases hx : G.Resonant x
  · exact Filter.Eventually.of_forall fun N => iff_of_true (G.resonant_prefix r N x hx) hx
  · have he : ¬G.Repeated r.val x := by rw [G.repeated_eq r hr]; exact hx
    unfold Repeated at he
    push Not at he
    obtain ⟨k,e,h⟩ := he
    filter_upwards [Filter.eventually_ge_atTop (k+1)] with N hN
    exact iff_of_false (fun hp => (not_lt.mpr h) (hp ⟨k,hN⟩ e)) hx

end Network

/-- The vacuum and one quantum of the prime two realize every phase as the time varies. -/
private theorem binary_phase_surjective (z : Circle) :
    ∃ (t : ℝ) (x : Bool → ℕ+), (binary t).phase () x = z := by
  obtain ⟨a,rfl⟩ := Circle.exp_surjective z
  let x (b : Bool) : ℕ+ := cond b 1 2
  have h : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  refine ⟨a / Real.log 2,x,?_⟩
  change Circle.exp (a / Real.log 2 * (energy 2 - energy 1)) = Circle.exp a
  have h₂ : energy 2 = Real.log 2 := by norm_num [energy]
  have h₁ : energy 1 = 0 := by simp [energy]
  rw [h₂,h₁,sub_zero,div_mul_cancel₀ _ h]

/-- The sharp universal detection radius already occurs on the physical two-copy gas. -/
theorem binary_repeated_radius_iff (r : {r : ℝ // 0 < r}) :
    (∀ t : ℝ, (binary t).Repeated r.val = (binary t).Resonant) ↔ r.val ≤ Real.sqrt 3 := by
  constructor
  · intro hall
    apply (dyadic_radius_iff r).mp
    intro z
    obtain ⟨t,x,he⟩ := binary_phase_surjective z
    constructor
    · intro h
      have hp : (binary t).Repeated r.val x := by
        rintro k ⟨⟩
        simpa only [Network.multiple_phase,he] using h k
      rw [hall t] at hp
      exact he.symm.trans (hp ())
    · rintro rfl k
      simpa only [one_pow,dist_self] using r.property
  · exact fun hr t => (binary t).repeated_eq r hr

/-- Every finite prefix accepts a word rejected by the exact sampled clock. -/
theorem binary_false_positive (t : {t : ℝ // t ≠ 0}) (r : {r : ℝ // 0 < r}) (N : ℕ) :
    ∃ x, (binary t.val).Prefix r.val N x ∧ ¬(binary t.val).Resonant x := by
  by_contra! h
  let G := binary t.val
  have he : G.Prefix r.val N = G.Resonant := by
    funext x
    exact propext ⟨h x,G.resonant_prefix r N x⟩
  have hs : HasSectorHeat G.Resonant (3/4) := by
    rw [binary_threshold,if_neg t.property]
    norm_num
  rw [← he] at hs
  have hb := (G.prefix_heat_iff r N (3/4)).mp hs
  norm_num at hb

/-- Words accepted by a finite prefix but rejected by the exact sampled clock. -/
def Network.falsePositives (G : Network I E) (r : ℝ) (N : ℕ) (x : I → ℕ+) : Prop :=
  G.Prefix r N x ∧ ¬G.Resonant x

private theorem heat_antitone [Fintype I] (s w : ℂ) (h : s.re ≤ w.re) (x : I → ℕ+) :
    ‖wordHeat w x‖ ≤ ‖wordHeat s x‖ := by
  simp only [Network.wordHeat_norm,Real.exp_le_exp]
  apply mul_le_mul_of_nonneg_right (neg_le_neg h)
  exact Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast (x i).pos)

/-- Finite-prefix false positives alone have heat boundary one at every nonzero binary time. -/
theorem false_positive_heat_iff (t : {t : ℝ // t ≠ 0}) (r : {r : ℝ // 0 < r}) (N : ℕ) (s : ℂ) :
    HasSectorHeat ((binary t.val).falsePositives r.val N) s ↔ 1 < s.re := by
  let G := binary t.val
  let P := G.Prefix r.val N
  let D := G.falsePositives r.val N
  rw [sectorHeat_iff]
  constructor
  · intro hs
    by_contra! hn
    have hd : AbsoluteHeat D 1 :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun x => heat_antitone s 1 hn x.val) hs
    have he : AbsoluteHeat G.Resonant 1 := (sectorHeat_iff _ _).mp
      ((binary_threshold t.val 1).mpr (by rw [if_neg t.property]; norm_num))
    let w (x : Bool → ℕ+) := ‖wordHeat 1 x‖
    have h₁ : Summable (Set.indicator {x | G.Resonant x} w) := summable_subtype_iff_indicator.mp he
    have h₂ : Summable (Set.indicator {x | D x} w) := summable_subtype_iff_indicator.mp hd
    have hu : Summable (Set.indicator {x | P x} w) := by
      refine (h₁.add h₂).congr fun x => ?_
      by_cases hx : G.Resonant x
      · have hpx := G.resonant_prefix r N x hx
        simp [P, D, Network.falsePositives, hx, hpx, w]
      · simp [Set.indicator_apply, P, D, Network.falsePositives, hx, w]
    have hp : AbsoluteHeat P 1 := summable_subtype_iff_indicator.mpr hu
    exact (lt_irrefl (1 : ℝ)) ((G.prefix_heat_iff r N 1).mp ((sectorHeat_iff _ _).mpr hp))
  · intro h
    have hp : AbsoluteHeat P s := (sectorHeat_iff _ _).mp ((G.prefix_heat_iff r N s).mpr h)
    let inc (x : {x // D x}) : {x // P x} := ⟨x.val,x.property.1⟩
    have hi : Function.Injective inc := fun _ _ he => Subtype.ext (congrArg (fun y : {x // P x} => y.val) he)
    exact hp.comp_injective (i := inc) hi

#print axioms Network.multiple_phase
#print axioms Network.repeated_eq
#print axioms Network.prefix_heat_iff
#print axioms Network.repeated_heat_iff
#print axioms Network.prefix_eventually
#print axioms binary_repeated_radius_iff
#print axioms binary_false_positive
#print axioms false_positive_heat_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
