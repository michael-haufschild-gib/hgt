import Mathlib

/-!
# Beurling generalized prime systems: finite Gibbs geometry and the depth-zero gauge

A discrete Beurling prime system is a family of prime labels carrying real norms greater than one;
its generalized integers are the free commutative monoid on those labels, with the multiplicative
norm.  Two parts of the local axiom package are pure label geometry and need no counting,
distribution or zero-free input at all: the squarefree exponential-Gibbs table is strictly
log-submodular in transverse directions, and the divided-log prime-power completion together with
its depth-zero Gamma gauge is exact.  Both are proved here for an arbitrary system.
-/

open scoped BigOperators

namespace RHTower

/-- A Beurling generalized prime system: prime labels with real norms exceeding one. -/
structure BeurlingSystem where
  /-- The type of prime labels. -/
  Label : Type
  /-- The norm of a prime label. -/
  labelNorm : Label → ℝ
  /-- Every generalized prime has norm greater than one. -/
  one_lt_labelNorm : ∀ p, 1 < labelNorm p

namespace BeurlingSystem

variable (B : BeurlingSystem)

/-- The generalized integers of a Beurling system: the free commutative monoid on prime labels. -/
abbrev Integer := Multiset B.Label

/-- The multiplicative norm of a generalized integer. -/
def intNorm (g : Multiset B.Label) : ℝ := (g.map B.labelNorm).prod

@[simp] theorem intNorm_zero : B.intNorm 0 = 1 := by
  rw [intNorm]
  simp

theorem intNorm_add (g h : Multiset B.Label) :
    B.intNorm (g + h) = B.intNorm g * B.intNorm h := by
  rw [intNorm, intNorm, intNorm, Multiset.map_add, Multiset.prod_add]

@[simp] theorem intNorm_singleton (p : B.Label) : B.intNorm {p} = B.labelNorm p := by
  rw [intNorm]
  simp

theorem one_le_intNorm (g : Multiset B.Label) : 1 ≤ B.intNorm g := by
  rw [intNorm]
  refine Multiset.one_le_prod fun x hx => ?_
  obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hx
  exact (B.one_lt_labelNorm p).le

theorem intNorm_pos (g : Multiset B.Label) : 0 < B.intNorm g :=
  lt_of_lt_of_le zero_lt_one (B.one_le_intNorm g)

theorem intNorm_replicate (p : B.Label) (k : ℕ) :
    B.intNorm (Multiset.replicate k p) = B.labelNorm p ^ k := by
  rw [intNorm, Multiset.map_replicate, Multiset.prod_replicate]

open scoped Classical in
/-- The generalized Möbius function: `(-1)^{ω}` on squarefree generalized integers, zero
elsewhere. -/
noncomputable def moebius (g : Multiset B.Label) : ℤ := if g.Nodup then (-1) ^ g.card else 0

open scoped Classical in
@[simp] theorem moebius_zero : B.moebius 0 = 1 := by
  rw [moebius, if_pos]
  · simp
  · exact Multiset.nodup_zero

open scoped Classical in
theorem moebius_cons_of_notMem {p : B.Label} {g : Multiset B.Label} (hp : p ∉ g) :
    B.moebius (p ::ₘ g) = -B.moebius g := by
  classical
  rw [moebius, moebius]
  by_cases hg : g.Nodup
  · rw [if_pos (Multiset.nodup_cons.mpr ⟨hp, hg⟩), if_pos hg, Multiset.card_cons, pow_succ]
    ring
  · rw [if_neg hg, if_neg fun h => hg (Multiset.nodup_cons.mp h).2]
    ring

/-! ## Möbius inversion over the free label monoid -/

open scoped Classical in
/-- **The generalized Möbius identity.**  Summing the generalized Möbius function over the divisors
of a generalized integer gives the unit indicator.  This is the algebraic input to the Dirichlet
inversion `∑_g μ_P(g)|g|^{-s} = ζ_P(s)^{-1}`. -/
theorem sum_moebius_divisors [DecidableEq B.Label] (g : Multiset B.Label) :
    ∑ d ∈ g.powerset.toFinset, B.moebius d = if g = 0 then 1 else 0 := by
  classical
  have hrestrict : ∑ d ∈ g.powerset.toFinset, B.moebius d
      = ∑ d ∈ g.powerset.toFinset.filter (fun d => d.Nodup), B.moebius d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [moebius]
    split_ifs with h
    · rfl
    · rfl
  have hbij : ∑ d ∈ g.powerset.toFinset.filter (fun d => d.Nodup), B.moebius d
      = ∑ S ∈ g.toFinset.powerset, (-1 : ℤ) ^ S.card := by
    refine Finset.sum_nbij' (fun d => d.toFinset) (fun S => S.val) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rw [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_powerset] at hd
      rw [Finset.mem_powerset]
      intro a ha
      rw [Multiset.mem_toFinset] at ha ⊢
      exact Multiset.mem_of_le hd.1 ha
    · intro S hS
      rw [Finset.mem_powerset] at hS
      rw [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_powerset]
      refine ⟨?_, S.nodup⟩
      rw [Multiset.le_iff_subset S.nodup]
      intro a ha
      have : a ∈ g.toFinset := hS ha
      rwa [Multiset.mem_toFinset] at this
    · intro d hd
      rw [Finset.mem_filter] at hd
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hd.2]
    · intro S _
      exact Finset.val_toFinset S
    · intro d hd
      rw [Finset.mem_filter] at hd
      rw [moebius, if_pos hd.2, Multiset.toFinset_card_of_nodup hd.2]
  rw [hrestrict, hbij, Finset.sum_powerset_neg_one_pow_card]
  by_cases hg : g = 0
  · rw [if_pos hg, if_pos (by rw [hg]; rfl)]
  · rw [if_neg hg, if_neg ?_]
    intro hcon
    exact hg (Multiset.toFinset_eq_empty.mp hcon)

/-! ## The finite Gibbs table -/

/-- The squarefree exponential-Gibbs weight `(BF2)` of a finite label set. -/
noncomputable def gibbsWeight (x : ℝ) (S : Finset B.Label) : ℝ :=
  Real.exp (-x * ∏ p ∈ S, B.labelNorm p)

theorem one_le_prod_labelNorm (S : Finset B.Label) : 1 ≤ ∏ p ∈ S, B.labelNorm p := by
  have h := Finset.prod_le_prod (s := S) (f := fun _ => (1 : ℝ)) (g := B.labelNorm)
    (fun i _ => zero_le_one) (fun i _ => (B.one_lt_labelNorm i).le)
  simpa using h

theorem one_lt_prod_labelNorm {S : Finset B.Label} (hS : S.Nonempty) :
    1 < ∏ p ∈ S, B.labelNorm p := by
  classical
  obtain ⟨p, hp⟩ := hS
  rw [← Finset.prod_erase_mul S _ hp]
  have h1 : 1 ≤ ∏ q ∈ S.erase p, B.labelNorm q := B.one_le_prod_labelNorm _
  have h2 : 1 < B.labelNorm p := B.one_lt_labelNorm p
  nlinarith

theorem prod_labelNorm_union [DecidableEq B.Label] (A C : Finset B.Label) :
    (∏ p ∈ A ∪ C, B.labelNorm p)
      = (∏ p ∈ A ∩ C, B.labelNorm p) * (∏ p ∈ A \ C, B.labelNorm p) *
          ∏ p ∈ C \ A, B.labelNorm p := by
  have hsplit : (∏ p ∈ A, B.labelNorm p)
      = (∏ p ∈ A ∩ C, B.labelNorm p) * ∏ p ∈ A \ C, B.labelNorm p :=
    (Finset.prod_inter_mul_prod_sdiff A C B.labelNorm).symm
  have hunion : A ∪ C = A ∪ (C \ A) := by
    rw [Finset.union_sdiff_self_eq_union]
  rw [hunion, Finset.prod_union Finset.disjoint_sdiff, hsplit]

/-- **Log-submodularity of the exponential-Gibbs table `(BF2)`.**  Every generalized prime norm
exceeds one, so the union/intersection pair never beats the two sets. -/
theorem gibbsWeight_mul_le [DecidableEq B.Label] {x : ℝ} (hx : 0 ≤ x) (A C : Finset B.Label) :
    B.gibbsWeight x (A ∪ C) * B.gibbsWeight x (A ∩ C)
      ≤ B.gibbsWeight x A * B.gibbsWeight x C := by
  set c : ℝ := ∏ p ∈ A ∩ C, B.labelNorm p with hc
  set r : ℝ := ∏ p ∈ A \ C, B.labelNorm p with hr
  set s : ℝ := ∏ p ∈ C \ A, B.labelNorm p with hs
  have hc1 : 1 ≤ c := B.one_le_prod_labelNorm _
  have hr1 : 1 ≤ r := B.one_le_prod_labelNorm _
  have hs1 : 1 ≤ s := B.one_le_prod_labelNorm _
  have hA : (∏ p ∈ A, B.labelNorm p) = c * r :=
    (Finset.prod_inter_mul_prod_sdiff A C B.labelNorm).symm
  have hC : (∏ p ∈ C, B.labelNorm p) = c * s := by
    have := (Finset.prod_inter_mul_prod_sdiff C A B.labelNorm).symm
    rwa [Finset.inter_comm C A] at this
  have hU : (∏ p ∈ A ∪ C, B.labelNorm p) = c * r * s := B.prod_labelNorm_union A C
  rw [gibbsWeight, gibbsWeight, gibbsWeight, gibbsWeight, hA, hC, hU, ← Real.exp_add,
    ← Real.exp_add, Real.exp_le_exp]
  have hkey : c * (r + s) ≤ c * (r * s + 1) := by
    have hrs : 0 ≤ (r - 1) * (s - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  nlinarith

/-- **Strict log-submodularity in transverse directions.**  When both set differences are
nonempty the inequality is strict, which is the conditional two-prime Rayleigh law. -/
theorem gibbsWeight_mul_lt [DecidableEq B.Label] {x : ℝ} (hx : 0 < x) {A C : Finset B.Label}
    (hAC : (A \ C).Nonempty) (hCA : (C \ A).Nonempty) :
    B.gibbsWeight x (A ∪ C) * B.gibbsWeight x (A ∩ C)
      < B.gibbsWeight x A * B.gibbsWeight x C := by
  set c : ℝ := ∏ p ∈ A ∩ C, B.labelNorm p with hc
  set r : ℝ := ∏ p ∈ A \ C, B.labelNorm p with hr
  set s : ℝ := ∏ p ∈ C \ A, B.labelNorm p with hs
  have hc1 : 1 ≤ c := B.one_le_prod_labelNorm _
  have hr1 : 1 < r := B.one_lt_prod_labelNorm hAC
  have hs1 : 1 < s := B.one_lt_prod_labelNorm hCA
  have hA : (∏ p ∈ A, B.labelNorm p) = c * r :=
    (Finset.prod_inter_mul_prod_sdiff A C B.labelNorm).symm
  have hC : (∏ p ∈ C, B.labelNorm p) = c * s := by
    have := (Finset.prod_inter_mul_prod_sdiff C A B.labelNorm).symm
    rwa [Finset.inter_comm C A] at this
  have hU : (∏ p ∈ A ∪ C, B.labelNorm p) = c * r * s := B.prod_labelNorm_union A C
  rw [gibbsWeight, gibbsWeight, gibbsWeight, gibbsWeight, hA, hC, hU, ← Real.exp_add,
    ← Real.exp_add, Real.exp_lt_exp]
  have hkey : c * (r + s) < c * (r * s + 1) := by
    have hrs : 0 < (r - 1) * (s - 1) := mul_pos (by linarith) (by linarith)
    nlinarith
  nlinarith

/-! ## The divided-log completion and the depth-zero gauge -/

/-- **The divided-log prime-power completion `(BF10)`.**  The generalized von Mangoldt value of a
prime power divided by its log-norm is the reciprocal depth. -/
theorem log_labelNorm_div_log_intNorm_replicate (p : B.Label) {k : ℕ} (hk : k ≠ 0) :
    Real.log (B.labelNorm p) / Real.log (B.intNorm (Multiset.replicate k p)) = 1 / k := by
  have hp1 : 1 < B.labelNorm p := B.one_lt_labelNorm p
  have hlog : 0 < Real.log (B.labelNorm p) := Real.log_pos hp1
  rw [intNorm_replicate, Real.log_pow]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The critical depth-zero Gamma gauge `(BF11)` of a generalized prime. -/
noncomputable def gammaGauge (p : B.Label) : ℝ := (1 - (B.labelNorm p)⁻¹)⁻¹

theorem one_lt_gammaGauge (p : B.Label) : 1 < B.gammaGauge p := by
  have hp1 : 1 < B.labelNorm p := B.one_lt_labelNorm p
  have hpos : 0 < B.labelNorm p := lt_trans zero_lt_one hp1
  have hinv : 0 < (B.labelNorm p)⁻¹ := inv_pos.mpr hpos
  have hlt : (B.labelNorm p)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hp1
  rw [gammaGauge, one_lt_inv_iff₀]
  constructor <;> linarith

theorem gammaGauge_le_two {p : B.Label} (hp : 2 ≤ B.labelNorm p) : B.gammaGauge p ≤ 2 := by
  have hpos : 0 < B.labelNorm p := lt_of_lt_of_le two_pos hp
  have hinv : (B.labelNorm p)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos] at *
    nlinarith [inv_pos.mpr hpos]
  have hden : (1 : ℝ) / 2 ≤ 1 - (B.labelNorm p)⁻¹ := by linarith
  rw [gammaGauge, inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- Deleting the labels of small norm from a system. -/
def truncate (c : ℝ) : BeurlingSystem where
  Label := {p : B.Label // c ≤ B.labelNorm p}
  labelNorm := fun p => B.labelNorm (p : B.Label)
  one_lt_labelNorm := fun p => B.one_lt_labelNorm (p : B.Label)

/-- **Bounded depth-zero gauge after deleting finitely many labels `(BF11)`.**  Once every
remaining generalized prime has norm at least two, the depth-zero Gamma gauge lies in `[1, 2]`. -/
theorem gammaGauge_mem_Icc_of_truncate (p : (B.truncate 2).Label) :
    (B.truncate 2).gammaGauge p ∈ Set.Icc (1 : ℝ) 2 :=
  ⟨((B.truncate 2).one_lt_gammaGauge p).le, (B.truncate 2).gammaGauge_le_two p.prop⟩

end BeurlingSystem

end RHTower
