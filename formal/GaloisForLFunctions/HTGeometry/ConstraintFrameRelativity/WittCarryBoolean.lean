import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.RamificationBooleanSupport
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.EscortLogit

/-!
# The binary Kummer carry is Boolean intersection

For two quadratic ramification stages the Kummer group is `(ℤ/4)^F` and the least-digit section
`σ : 𝒫(F) → (ℤ/4)^F` has section defect exactly the Boolean meet:

`σ(S) + σ(T) = σ(S △ T) + 2 σ(S ∩ T)`,   `κ₂(S,T) = S ∩ T`,

so addition in the digit coordinates is the length-two Witt law
`(S,A) ⋆ (T,B) = (S △ T, A △ B △ (S ∩ T))`, whose associativity is the cocycle identity.  The
extension does not split: a lift of a nonzero mod-two basis vector has order four.

On the ramification diagonal the level-`m` shell activity of a product is exactly the zero-carry
locus, and the exact integer identity `k^m l^m = (k/g)^m (l/g)^m g^{2m}` isolates the discarded
repeat-occupancy factor.  For two independent Boolean gases the carry statistics are
`E|S ∩ T| = ∑ q_p u_p` and `P(S ∩ T = ∅) = ∏ (1 - q_p u_p)`, and the marked three-storey history
closes mod two after two steps, lands on the kernel point `2σ(S)` mod four, and never closes
integrally.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## The least-digit section and its carry -/

/-- The least nonnegative digit section of a Boolean configuration. -/
def digitSection (S : Finset ι) (p : ι) : ZMod 4 := if p ∈ S then 1 else 0

/-- **Boolean meet is the Kummer carry.** -/
theorem digitSection_add (S T : Finset ι) :
    digitSection S + digitSection T
      = digitSection (symmDiff S T) + 2 • digitSection (S ∩ T) := by
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, digitSection, Finset.mem_symmDiff, Finset.mem_inter]
  by_cases hS : p ∈ S <;> by_cases hT : p ∈ T <;> simp [hS, hT]
  decide

/-- **The length-two Witt addition law.** -/
theorem witt_add (S A T B : Finset ι) :
    (digitSection S + 2 • digitSection A) + (digitSection T + 2 • digitSection B)
      = digitSection (symmDiff S T) + 2 • digitSection (symmDiff (symmDiff A B) (S ∩ T)) := by
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, digitSection, Finset.mem_symmDiff, Finset.mem_inter]
  by_cases hS : p ∈ S <;> by_cases hT : p ∈ T <;> by_cases hA : p ∈ A <;> by_cases hB : p ∈ B <;>
    simp [hS, hT, hA, hB]
  all_goals decide

/-- **The carry cocycle identity.** -/
theorem carry_cocycle (S T R : Finset ι) :
    symmDiff (S ∩ T) (symmDiff S T ∩ R) = symmDiff (T ∩ R) (S ∩ symmDiff T R) := by
  ext p
  simp only [Finset.mem_symmDiff, Finset.mem_inter]
  tauto

/-- The carry of a set with itself is the set. -/
theorem carry_self (S : Finset ι) : S ∩ S = S := Finset.inter_self S

/-- **The extension is nonsplit.**  No additive section of the mod-two reduction exists once a
coordinate is available: every lift of a nonzero mod-two vector has order four. -/
theorem no_group_section (p : ι) (f : (ι → ZMod 2) →+ (ι → ZMod 4))
    (hf : ∀ (x : ι → ZMod 2) (q : ι),
      ZMod.castHom (show (2 : ℕ) ∣ 4 by norm_num) (ZMod 2) (f x q) = x q) : False := by
  classical
  set e : ι → ZMod 2 := fun q => if q = p then 1 else 0 with he
  have h2e : (2 : ℕ) • e = 0 := by
    funext q
    simp only [Pi.smul_apply, Pi.zero_apply, he]
    by_cases hq : q = p
    · subst hq
      simp
      decide
    · simp [hq]
  have hfe : (2 : ℕ) • f e = 0 := by
    rw [← map_nsmul, h2e, map_zero]
  have hval : ZMod.castHom (show (2 : ℕ) ∣ 4 by norm_num) (ZMod 2) (f e p) = 1 := by
    rw [hf e p, he]
    simp
  have hcoord : (2 : ℕ) • (f e p) = 0 := by
    have h := congrFun hfe p
    simpa using h
  revert hval hcoord
  generalize f e p = z
  revert z
  decide

/-! ## The hard-core law on the ramification diagonal -/

/-- **Shell activity is zero carry.** -/
theorem unitalShellIndicator_mul_pow_eq_one_iff {m k l : ℕ} (hm : m ≠ 0) (hk : k ≠ 0)
    (hl : l ≠ 0) (hks : Squarefree k) (hls : Squarefree l) :
    unitalShellIndicator m ((k * l) ^ m) = 1 ↔ Nat.Coprime k l := by
  rw [unitalShellIndicator_pow_self_eq_one_iff hm (Nat.mul_ne_zero hk hl),
    Nat.squarefree_mul_iff]
  constructor
  · rintro ⟨h, -, -⟩
    exact h
  · intro h
    exact ⟨h, hks, hls⟩

/-- **The exact integer identity.**  The discarded factor is the squared common part. -/
theorem pow_mul_pow_eq (m k l : ℕ) :
    k ^ m * l ^ m
      = (k / Nat.gcd k l) ^ m * (l / Nat.gcd k l) ^ m * (Nat.gcd k l) ^ (2 * m) := by
  have hdk : Nat.gcd k l ∣ k := Nat.gcd_dvd_left k l
  have hdl : Nat.gcd k l ∣ l := Nat.gcd_dvd_right k l
  have hk' : k / Nat.gcd k l * Nat.gcd k l = k := Nat.div_mul_cancel hdk
  have hl' : l / Nat.gcd k l * Nat.gcd k l = l := Nat.div_mul_cancel hdl
  calc k ^ m * l ^ m
      = (k / Nat.gcd k l * Nat.gcd k l) ^ m * (l / Nat.gcd k l * Nat.gcd k l) ^ m := by
        rw [hk', hl']
    _ = (k / Nat.gcd k l) ^ m * (l / Nat.gcd k l) ^ m * (Nat.gcd k l) ^ (2 * m) := by
        rw [mul_pow, mul_pow, two_mul, pow_add]
        ring

/-! ## Carry statistics of two independent Boolean gases -/

variable [Fintype ι]

/-- Joint expectation of two independent Boolean gases. -/
def jointExp (q u : ι → ℝ) (f : Finset ι → Finset ι → ℝ) : ℝ :=
  ∑ S : Finset ι, ∑ T : Finset ι, bernoulliWeight q S * bernoulliWeight u T * f S T

theorem prod_split_mem (T : Finset ι) (k : ι → Bool → ℝ) :
    ∏ p, k p (decide (p ∈ T)) = (∏ p ∈ T, k p true) * ∏ p ∈ Tᶜ, k p false := by
  rw [← Finset.prod_mul_prod_compl T (fun p => k p (decide (p ∈ T)))]
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by simp [hp]
  · exact Finset.prod_congr rfl fun p hp => by simp [Finset.mem_compl.mp hp]

/-- **The per-site product law for two independent gases.** -/
theorem jointExp_prod (q u : ι → ℝ) (h : ι → Bool → Bool → ℝ) :
    jointExp q u (fun S T => ∏ p, h p (decide (p ∈ S)) (decide (p ∈ T)))
      = ∏ p, (q p * u p * h p true true + q p * (1 - u p) * h p true false
          + (1 - q p) * u p * h p false true + (1 - q p) * (1 - u p) * h p false false) := by
  have hinner : ∀ S : Finset ι,
      ∑ T : Finset ι, bernoulliWeight u T * ∏ p, h p (decide (p ∈ S)) (decide (p ∈ T))
        = ∏ p, (u p * h p (decide (p ∈ S)) true
            + (1 - u p) * h p (decide (p ∈ S)) false) := by
    intro S
    have hrw : ∀ T : Finset ι, (∏ p, h p (decide (p ∈ S)) (decide (p ∈ T)))
        = (∏ p ∈ T, h p (decide (p ∈ S)) true) * ∏ p ∈ Tᶜ, h p (decide (p ∈ S)) false :=
      fun T => prod_split_mem T (fun p b => h p (decide (p ∈ S)) b)
    have := bernoulliExp_prod u (fun p => h p (decide (p ∈ S)) true)
      (fun p => h p (decide (p ∈ S)) false)
    rw [bernoulliExp] at this
    rw [Finset.sum_congr rfl fun T _ => by rw [hrw T]]
    exact this
  have houter : ∀ S : Finset ι, ∀ p : ι,
      (u p * h p (decide (p ∈ S)) true + (1 - u p) * h p (decide (p ∈ S)) false)
        = (fun b => u p * h p b true + (1 - u p) * h p b false) (decide (p ∈ S)) := fun _ _ => rfl
  rw [jointExp]
  have hstep : ∑ S : Finset ι, ∑ T : Finset ι,
      bernoulliWeight q S * bernoulliWeight u T * ∏ p, h p (decide (p ∈ S)) (decide (p ∈ T))
      = ∑ S : Finset ι, bernoulliWeight q S *
          ∏ p, (fun b => u p * h p b true + (1 - u p) * h p b false) (decide (p ∈ S)) := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← hinner S, Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [hstep]
  have hfin := bernoulliExp_prod q
    (fun p => u p * h p true true + (1 - u p) * h p true false)
    (fun p => u p * h p false true + (1 - u p) * h p false false)
  rw [bernoulliExp] at hfin
  have hrw2 : ∀ S : Finset ι,
      (∏ p, (fun b => u p * h p b true + (1 - u p) * h p b false) (decide (p ∈ S)))
        = (∏ p ∈ S, (u p * h p true true + (1 - u p) * h p true false))
          * ∏ p ∈ Sᶜ, (u p * h p false true + (1 - u p) * h p false false) :=
    fun S => prod_split_mem S (fun p b => u p * h p b true + (1 - u p) * h p b false)
  rw [Finset.sum_congr rfl fun S _ => by rw [hrw2 S]]
  rw [hfin]
  exact Finset.prod_congr rfl fun p _ => by ring

/-- **Zero-carry probability.** -/
theorem jointExp_empty_carry (q u : ι → ℝ) :
    jointExp q u (fun S T => if S ∩ T = ∅ then 1 else 0)
      = ∏ p, (1 - q p * u p) := by
  have hind : ∀ S T : Finset ι, (if S ∩ T = ∅ then (1 : ℝ) else 0)
      = ∏ p, (fun (b c : Bool) => if b && c then (0 : ℝ) else 1)
          (decide (p ∈ S)) (decide (p ∈ T)) := by
    intro S T
    by_cases h : S ∩ T = ∅
    · rw [if_pos h]
      refine (Finset.prod_eq_one fun p _ => ?_).symm
      have hp : ¬ (p ∈ S ∧ p ∈ T) := by
        intro hpi
        have hmem : p ∈ S ∩ T := Finset.mem_inter.mpr hpi
        rw [h] at hmem
        simp at hmem
      by_cases hS : p ∈ S <;> by_cases hT : p ∈ T <;> simp_all
    · rw [if_neg h]
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr h
      obtain ⟨hpS, hpT⟩ := Finset.mem_inter.mp hp
      refine (Finset.prod_eq_zero (Finset.mem_univ p) ?_).symm
      simp [hpS, hpT]
  calc jointExp q u (fun S T => if S ∩ T = ∅ then (1 : ℝ) else 0)
      = jointExp q u (fun S T => ∏ p, (fun (_ : ι) (b c : Bool) =>
          if b && c then (0 : ℝ) else 1) p (decide (p ∈ S)) (decide (p ∈ T))) := by
        congr 1
        funext S T
        exact hind S T
    _ = ∏ p, (q p * u p * 0 + q p * (1 - u p) * 1
        + (1 - q p) * u p * 1 + (1 - q p) * (1 - u p) * 1) := by
        simpa using jointExp_prod q u (fun (_ : ι) (b c : Bool) => if b && c then (0 : ℝ) else 1)
    _ = ∏ p, (1 - q p * u p) := Finset.prod_congr rfl fun p _ => by ring

/-- Expectation of a sum of independent products factorises coordinatewise. -/
theorem jointExp_sum_prod (q u : ι → ℝ) (f g : ι → Finset ι → ℝ) :
    jointExp q u (fun S T => ∑ p, f p S * g p T)
      = ∑ p, bernoulliExp q (f p) * bernoulliExp u (g p) := by
  rw [jointExp]
  have h1 : ∀ S T : Finset ι,
      bernoulliWeight q S * bernoulliWeight u T * (∑ p, f p S * g p T)
        = ∑ p, (bernoulliWeight q S * f p S) * (bernoulliWeight u T * g p T) := by
    intro S T
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => h1 S T]
  rw [Finset.sum_congr rfl fun S _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bernoulliExp, bernoulliExp, Finset.sum_mul_sum]

/-- **Expected carry size.** -/
theorem jointExp_carry_card (q u : ι → ℝ) :
    jointExp q u (fun S T => ((S ∩ T).card : ℝ)) = ∑ p, q p * u p := by
  have hcard : ∀ S T : Finset ι, ((S ∩ T).card : ℝ)
      = ∑ p, (if p ∈ S then (1 : ℝ) else 0) * (if p ∈ T then (1 : ℝ) else 0) := by
    intro S T
    have hpt : ∀ p : ι, (if p ∈ S then (1 : ℝ) else 0) * (if p ∈ T then (1 : ℝ) else 0)
        = if p ∈ S ∩ T then (1 : ℝ) else 0 := by
      intro p
      by_cases hS : p ∈ S <;> by_cases hT : p ∈ T <;> simp [hS, hT, Finset.mem_inter]
    rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_ite_mem, Finset.univ_inter]
    simp
  rw [show (fun S T : Finset ι => ((S ∩ T).card : ℝ))
      = fun S T => ∑ p, (if p ∈ S then (1 : ℝ) else 0) * (if p ∈ T then (1 : ℝ) else 0) from
    funext fun S => funext fun T => hcard S T]
  rw [jointExp_sum_prod]
  exact Finset.sum_congr rfl fun p _ => by
    rw [bernoulliExp_mem, bernoulliExp_mem]

/-- **Replica carry statistics.**  Two replicas of the same Gibbs law. -/
theorem jointExp_carry_card_self (q : ι → ℝ) :
    jointExp q q (fun S T => ((S ∩ T).card : ℝ)) = ∑ p, q p ^ (2 : ℕ) := by
  rw [jointExp_carry_card]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem jointExp_empty_carry_self (q : ι → ℝ) :
    jointExp q q (fun S T => if S ∩ T = ∅ then 1 else 0) = ∏ p, (1 - q p ^ (2 : ℕ)) := by
  rw [jointExp_empty_carry]
  exact Finset.prod_congr rfl fun p _ => by ring

omit [Fintype ι] in
/-- The replica zero-carry factor of a fugacity. -/
theorem one_sub_sq_oddsToProb {x : ℝ} (hx : 0 < x) :
    1 - (oddsToProb x) ^ (2 : ℕ) = (1 + 2 * x) / (1 + x) ^ (2 : ℕ) := by
  have hd : (1 : ℝ) + x ≠ 0 := by linarith
  rw [oddsToProb]
  field_simp
  ring

omit [Fintype ι] in
/-- **The conditional carry probability is the second escort.** -/
theorem conditional_carry_eq_escort (q : ℝ) :
    q * q / (q * q + (1 - q) * (1 - q)) = escortMap 2 q := by
  rw [escortMap]
  ring_nf

/-! ## The marked three-storey history -/

/-- The marked integral history of a Boolean configuration. -/
def markedHistory (S : Finset ι) (n : ℕ) (p : ι) : ℤ := if p ∈ S then (n : ℤ) else 0

omit [Fintype ι] in
/-- The mod-two observer closes after two steps. -/
theorem markedHistory_mod_two (S : Finset ι) (p : ι) :
    ((markedHistory S 2 p : ℤ) : ZMod 2) = 0 := by
  rw [markedHistory]
  by_cases h : p ∈ S <;> simp [h]
  decide

omit [Fintype ι] in
/-- The mod-four lift does not close after two steps: it lands on `2 σ(S)`. -/
theorem markedHistory_mod_four_two (S : Finset ι) (p : ι) :
    ((markedHistory S 2 p : ℤ) : ZMod 4) = 2 • digitSection S p := by
  rw [markedHistory, digitSection]
  by_cases h : p ∈ S <;> simp [h]

omit [Fintype ι] in
/-- The mod-four lift closes after four steps. -/
theorem markedHistory_mod_four_four (S : Finset ι) (p : ι) :
    ((markedHistory S 4 p : ℤ) : ZMod 4) = 0 := by
  rw [markedHistory]
  by_cases h : p ∈ S <;> simp [h]
  decide

omit [Fintype ι] in
/-- The kernel point is nonzero for a nonempty configuration. -/
theorem two_digitSection_ne_zero {S : Finset ι} (hS : S.Nonempty) :
    2 • digitSection S ≠ 0 := by
  obtain ⟨p, hp⟩ := hS
  intro h
  have hcoord := congrFun h p
  rw [Pi.smul_apply, digitSection, if_pos hp] at hcoord
  have hne : (2 : ℕ) • (1 : ZMod 4) ≠ (0 : ZMod 4) := by decide
  exact hne hcoord

/-- The integral history never closes, and its norm grows linearly. -/
theorem sum_sq_markedHistory (S : Finset ι) (n : ℕ) :
    ∑ p, ((markedHistory S n p : ℤ) : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℕ) * S.card := by
  have hpt : ∀ p : ι, ((markedHistory S n p : ℤ) : ℝ) ^ (2 : ℕ)
      = if p ∈ S then ((n : ℝ) ^ (2 : ℕ)) else 0 := by
    intro p
    rw [markedHistory]
    by_cases h : p ∈ S <;> simp [h]
  rw [Finset.sum_congr rfl fun p _ => hpt p]
  simp [Finset.sum_ite_mem, mul_comm]

end HTGeometry.ConstraintFrameRelativity
