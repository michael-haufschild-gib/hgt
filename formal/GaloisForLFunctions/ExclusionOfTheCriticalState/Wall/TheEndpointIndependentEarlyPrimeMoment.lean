import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SquareRootBlocksInTheActualMixedPrimeMoment

/-!
# The endpoint-independent early prime moment

In the first numerator slab both signed discrepancies equal those of
the terminal half of the same numerator. The band width enters the
early moment only through its external factor L. Removing that factor
gives one arithmetic sequence, with no band-width or eligibility
exponent, whose one-sided moment bounds characterize RH. The infimum of
the admissible gate powers is the zero abscissa minus one half. The
square-root gate itself has unbounded normalized moments in either sign.
-/

open Filter Finset
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

private def terminalPass (s A : ℝ) (H : ℕ) : Prop :=
  A*Real.sqrt H<s*terminalOddHalf H ∧
    A*Real.sqrt H<(-s)*oddQuotientPrimeExcess (middleTestFlank true (H/2) H H) H

/-- Moment of the universal terminal prices in the first numerator
slab, with only their two arithmetic gates surviving. -/
def terminalSlabMoment (s a g : ℝ) (X : ℕ) : ℝ := by
  classical
  exact X*∑ H ∈ (Icc X (X+X/2)).filter (terminalPass s (a*Real.exp (g*Real.log X))),
    terminalJointHeight s H/(H:ℝ)

/-- The original early moment divided by L is independent of η and d
at all sufficiently large observation scales. -/
theorem exact_early_moment_rescaling (s a g : ℝ) {d η : ℝ} (hd : d≤1/4) (hη : 0<η) :
    ∀ᶠ X : ℕ in atTop, (X:ℝ)*earlyHalfCutMoment s a g d η X=
      (terminalBandEndpoint η X:ℝ)*terminalSlabMoment s a g X := by
  classical
  have grow : Tendsto (fun X : ℕ => (X:ℝ)^η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop 2,eventually_ge_atTop 16] with X big hX
  let L := terminalBandEndpoint η X
  let D := Icc X (X+X/2)
  let N := largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) L
  let test := terminalPass s (a*Real.exp (g*Real.log X))
  have xp : 0<(X:ℝ) := Nat.cast_pos.mpr (by omega)
  have xl : 2*X≤L := by
    have low : (X:ℝ)^(1+η)≤(L:ℝ) := by
      rw [Real.rpow_def_of_pos xp,mul_comm (Real.log X) (1+η)]
      exact Nat.le_ceil _
    rw [Real.rpow_add xp,Real.rpow_one] at low
    have h := (mul_le_mul_of_nonneg_left big xp.le).trans low
    rw [mul_comm (X:ℝ) 2] at h
    exact_mod_cast h
  have row {H : ℕ} (h : H∈D) : (H∈N ↔ test H) ∧
      oppositePrimeProduct true s (X/2) L H=terminalJointHeight s H/(H:ℝ) := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp h
    have cut : X/2≤H/2 := by omega
    have third : H<3*(X/2+1) := by omega
    have hl : H≤L := by omega
    obtain ⟨mid,side⟩ := second_quotient_cut_invariance cut third hl
    have eligible := initial_slab_middle_eligible hX lo (by omega) hl hd
    constructor
    · simp only [N,largeOppositePrimeNumerators,mem_filter,eligible,true_and,←mid,side,test,terminalPass]
    · apply (eq_div_iff (Nat.cast_pos.mpr (show 0<H by omega) : 0<(H:ℝ)).ne').mpr
      rw [mul_comm]
      exact second_quotient_joint_price s cut third hl
  have set_eq : N ∩ D=D.filter test := by
    ext H
    simp only [mem_inter,mem_filter]
    exact ⟨fun h => ⟨h.2,(row h.2).1.mp h.1⟩,fun h => ⟨(row h.1).1.mpr h.2,h.1⟩⟩
  have same : (∑ H ∈ N ∩ D,oppositePrimeProduct true s (X/2) L H)=
      ∑ H ∈ D.filter test,terminalJointHeight s H/(H:ℝ) := by
    rw [set_eq]
    exact sum_congr rfl fun H h => (row (mem_filter.mp h).1).2
  change (X:ℝ)*((L:ℝ)*(∑ H ∈ N ∩ D,oppositePrimeProduct true s (X/2) L H))=
    (L:ℝ)*((X:ℝ)*(∑ H ∈ D.filter test,terminalJointHeight s H/(H:ℝ)))
  rw [same]
  ring

private theorem normalized_at_unit_width (s a g : ℝ) :
    ∀ᶠ X : ℕ in atTop, earlyHalfCutMoment s a g 0 1 X=(X:ℝ)*terminalSlabMoment s a g X := by
  filter_upwards [exact_early_moment_rescaling s a g (by norm_num : (0:ℝ)≤1/4) (zero_lt_one),
    eventually_ge_atTop 1] with X h hX
  have xp : 0<(X:ℝ) := Nat.cast_pos.mpr hX
  have square : Real.exp ((1+1)*Real.log X)=(X:ℝ)^2 := by
    rw [←Real.rpow_two,Real.rpow_def_of_pos xp]
    congr 1
    ring
  have L : terminalBandEndpoint 1 X=X^2 := by
    unfold terminalBandEndpoint
    rw [square,←Nat.cast_pow,Nat.ceil_natCast]
  rw [L,Nat.cast_pow] at h
  apply (mul_left_cancel₀ xp.ne')
  linarith only [h]

private theorem unit_bound_iff (s a g : ℝ) :
    (∃ M : ℝ, 0≤M ∧ ∀ᶠ X : ℕ in atTop, earlyHalfCutMoment s a g 0 1 X≤M*(X:ℝ)^(1/2+1+3*g)) ↔
      ∃ M : ℝ, 0≤M ∧ ∀ᶠ X : ℕ in atTop, terminalSlabMoment s a g X≤M*(X:ℝ)^(1/2+3*g) := by
  have factor {x : ℝ} (hp : 0<x) (g : ℝ) : x^(1/2+1+3*g)=x*x^(1/2+3*g) := by
    rw [show (1/2:ℝ)+1+3*g=1+(1/2+3*g) by ring,Real.rpow_add hp,Real.rpow_one]
  constructor
  · rintro ⟨M,hM,cap⟩
    refine ⟨M,hM,?_⟩
    filter_upwards [cap,normalized_at_unit_width s a g,eventually_ge_atTop 1] with X h eq hX
    have xp : 0<(X:ℝ) := Nat.cast_pos.mpr hX
    rw [eq,factor xp,mul_left_comm M (X:ℝ)] at h
    exact le_of_mul_le_mul_left h xp
  · rintro ⟨M,hM,cap⟩
    refine ⟨M,hM,?_⟩
    filter_upwards [cap,normalized_at_unit_width s a g,eventually_ge_atTop 1] with X h eq hX
    have xp : 0<(X:ℝ) := Nat.cast_pos.mpr hX
    rw [eq,factor xp,mul_left_comm M (X:ℝ)]
    exact mul_le_mul_of_nonneg_left h xp.le

private theorem width_of_single_gate_bound {s a g : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a) (hg : 0≤g)
    (cap : ∃ M : ℝ, 0≤M ∧ ∀ᶠ X : ℕ in atTop, terminalSlabMoment s a g X≤M*(X:ℝ)^(1/2+3*g)) :
    zeroReSup≤g+1/2 := by
  have eq : (1/2+1+3*g+1-1)/3=g+1/2 := by ring
  rcases half_cut_moment_or_zero_abscissa (t:=1/2+1+3*g) hs ha hg (by norm_num : (0:ℝ)≤1/4)
      zero_lt_one with width|large
  · simpa only [eq,max_self] using width
  · obtain ⟨M,hM,paid⟩ := (unit_bound_iff s a g).mpr cap
    obtain ⟨X,above,below⟩ := ((large M hM).and_eventually paid).exists
    exact False.elim (above.not_ge below)

/-- With one sign and one positive coefficient, moment bounds at the
gate powers above c−1/2 characterize the entire zero-free half-plane
to the right of c. -/
theorem terminal_slab_zero_width {s a c : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a) (hc : 1/2≤c) :
    zeroReSup≤c ↔ ∀ g : ℝ, c<g+1/2 → ∃ M : ℝ, 0≤M ∧
      ∀ᶠ X : ℕ in atTop, terminalSlabMoment s a g X≤M*(X:ℝ)^(1/2+3*g) := by
  constructor
  · intro bound g hg
    apply (unit_bound_iff s a g).mp
    refine ⟨0,le_rfl,?_⟩
    filter_upwards [initial_half_cut_eventually_empty (d:=0) hs ha (bound.trans_lt hg) zero_lt_one] with X empty
    simp only [earlyHalfCutMoment,Finset.disjoint_iff_inter_eq_empty.mp empty.symm,sum_empty,mul_zero,zero_mul,le_refl]
  · intro all
    by_contra! wide
    let g := (c+zeroReSup)/2-1/2
    have low : c<g+1/2 := by dsimp only [g]; linarith only [wide]
    have high : g+1/2<zeroReSup := by dsimp only [g]; linarith only [wide]
    have pg : 0≤g := by linarith only [hc,low]
    exact high.not_ge (width_of_single_gate_bound hs ha pg (all g low))

/-- The last-half moment requires one sign and one positive scale
coefficient. Its bound X^(1/2+3g) for every positive gate power g is
equivalent to RH. -/
theorem rh_iff_terminal_slab_moment {s a : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a) :
    RiemannHypothesis ↔ ∀ g : ℝ, 0<g → ∃ M : ℝ, 0≤M ∧
      ∀ᶠ X : ℕ in atTop, terminalSlabMoment s a g X≤M*(X:ℝ)^(1/2+3*g) := by
  have width : RiemannHypothesis ↔ zeroReSup≤1/2 :=
    ⟨fun rh => (ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_zeroReSup_eq_half.mp rh).le,
      ArithmeticOfSquareRootPrecision.riemannHypothesis_of_zeroReSup_le_half⟩
  rw [width,terminal_slab_zero_width hs ha le_rfl]
  exact ⟨fun h g hg => h g (by linarith only [hg]),fun h g hg => h g (by linarith only [hg])⟩

/-- At the square-root gate the normalized moment in either specified
sign exceeds every square-root multiple infinitely often. -/
theorem terminal_slab_square_root_excursions {s a : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a)
    (M : ℝ) (hM : 0≤M) :
    ∃ᶠ X : ℕ in atTop, M*Real.sqrt X<terminalSlabMoment s a 0 X := by
  have hR : 1≤4*(M+1) := by linarith only [hM]
  have blocks := square_root_blocks_in_mixed_prime_moment hs ha (by norm_num : (0:ℝ)≤1/4)
    zero_lt_one (4*(M+1)) 1 hR zero_lt_one
  apply ((blocks.and_eventually (normalized_at_unit_width s a 0)).and_eventually
    (eventually_ge_atTop 1)).mono
  rintro X ⟨⟨block,scale⟩,hX⟩
  have xp : 0<(X:ℝ) := Nat.cast_pos.mpr hX
  have paid := block.2.2
  change 4*(M+1)*1^2/4*(X:ℝ)^((1/2:ℝ)+1)≤earlyHalfCutMoment s a 0 0 1 X at paid
  rw [scale,Real.rpow_add xp,←Real.sqrt_eq_rpow,Real.rpow_one] at paid
  have large : ((M+1)*Real.sqrt X)*(X:ℝ)≤terminalSlabMoment s a 0 X*(X:ℝ) := by linarith only [paid]
  exact (mul_lt_mul_of_pos_right (lt_add_one M) (Real.sqrt_pos.mpr xp)).trans_le (le_of_mul_le_mul_right large xp)

/-- Nonnegative powers of the gate for which the one-sign normalized
moment satisfies its polynomial bound. -/
def boundedTerminalGatePowers (s a : ℝ) : Set ℝ :=
  {g | 0≤g ∧ ∃ M : ℝ, 0≤M ∧ ∀ᶠ X : ℕ in atTop, terminalSlabMoment s a g X≤M*(X:ℝ)^(1/2+3*g)}

/-- The infimum of the bounded gate powers recovers the zero width
numerically from just one orientation of the terminal test. -/
theorem terminal_gate_infimum {s a : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a) :
    sInf (boundedTerminalGatePowers s a)=zeroReSup-1/2 := by
  let B := boundedTerminalGatePowers s a
  have low : ∀ g∈B, zeroReSup-1/2≤g := fun g hg => by
    have bound := width_of_single_gate_bound hs ha hg.1 hg.2
    linarith only [bound]
  have above {g : ℝ} (h : zeroReSup-1/2<g) : g∈B := by
    have wide : zeroReSup<g+1/2 := by linarith only [h]
    refine ⟨by linarith only [h,half_le_zeroReSup],?_⟩
    exact (terminal_slab_zero_width hs ha half_le_zeroReSup).mp le_rfl g wide
  have ne : B.Nonempty := ⟨zeroReSup,above (by linarith only)⟩
  have floor : BddBelow B := ⟨zeroReSup-1/2,low⟩
  change sInf B=_
  apply le_antisymm _ (le_csInf ne low)
  by_contra! gap
  let g := (zeroReSup-1/2+sInf B)/2
  have left : zeroReSup-1/2<g := by dsimp [g]; linarith only [gap]
  have right : g<sInf B := by dsimp [g]; linarith only [gap]
  exact right.not_ge (csInf_le floor (above left))

/-- RH holds exactly when the bounded powers form the open positive
ray. Its left endpoint fails independently of the zero distribution. -/
theorem rh_iff_bounded_terminal_gates {s a : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a) :
    RiemannHypothesis ↔ boundedTerminalGatePowers s a=Set.Ioi 0 := by
  constructor
  · intro rh
    ext g
    constructor
    · rintro ⟨hg,cap⟩
      apply hg.lt_of_ne
      rintro rfl
      obtain ⟨M,hM,paid⟩ := cap
      simp only [mul_zero,add_zero,←Real.sqrt_eq_rpow] at paid
      obtain ⟨X,above,below⟩ := ((terminal_slab_square_root_excursions hs ha M hM).and_eventually paid).exists
      exact above.not_ge below
    · intro hg
      exact ⟨le_of_lt hg,(rh_iff_terminal_slab_moment hs ha).mp rh g hg⟩
  · intro eq
    apply (rh_iff_terminal_slab_moment hs ha).mpr
    intro g hg
    have hit : g∈boundedTerminalGatePowers s a := by rw [eq]; exact hg
    exact hit.2

#print axioms terminal_gate_infimum
#print axioms terminal_slab_square_root_excursions
#print axioms rh_iff_bounded_terminal_gates
#print axioms exact_early_moment_rescaling
#print axioms terminal_slab_zero_width
#print axioms rh_iff_terminal_slab_moment
end GaloisForLFunctions.ExclusionOfTheCriticalState
