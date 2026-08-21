/-
# Averaging a low-frequency trigonometric polynomial over an eighth-root ensemble

A finite ensemble whose evaluation vector is uniform on every set of at most `K` coordinates
reproduces the Haar mean of every trigonometric polynomial whose frequencies are supported on at
most `K` coordinates and whose entries are smaller than eight in absolute value: each nonzero
character averages to zero on both sides, and the zero character to one.  This is the transfer that
carries the continuous-phase collision moments to a finite phase alphabet.

Main results:
* `eighthPhase` — the real phase vector of an eighth-root residue vector.
* `charLift_eighthPhase` — a character at an eighth-root phase is a product of eighth-root
  characters.
* `sum_charLift_eighthPhase_eq_zero` — a low-frequency nonzero character averages to zero.
* `sum_trigLift_eighthPhase_eq_freqBlock_zero` — **the ensemble mean of a low-frequency
  trigonometric polynomial is its zero-frequency coefficient**, the same value as its Haar mean.
-/
import GaloisForLFunctions.HTGeometry.EighthRootMomentTransfer
import GaloisForLFunctions.HTGeometry.TorusTrigPoincare

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The real phase vector attached to a vector of eighth-root residues. -/
def eighthPhase (w : α → ZMod 8) : α → ℝ := fun a => ((w a).val : ℝ) / 8

theorem zeta8_pow_eight : zeta8 ^ (8 : ℕ) = 1 := isPrimitiveRoot_zeta8.pow_eq_one

theorem zeta8_zpow_eight : zeta8 ^ (8 : ℤ) = 1 := by
  rw [show ((8 : ℤ)) = ((8 : ℕ) : ℤ) from rfl, zpow_natCast]
  exact zeta8_pow_eight

theorem zeta8_zpow_eq_charEight (m : ℤ) : zeta8 ^ m = charEight ((m : ZMod 8)) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : ℕ, v = ((m : ZMod 8)).val := ⟨_, rfl⟩
  have hcast : (((v : ℕ) : ℤ) : ZMod 8) = ((m : ℤ) : ZMod 8) := by
    rw [hv]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hdvd : ((8 : ℕ) : ℤ) ∣ m - (v : ℤ) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (m - (v : ℤ)) 8).mp ?_
    rw [Int.cast_sub, hcast, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  have hm : m = (v : ℤ) + 8 * q := by
    have hq' : m - (v : ℤ) = 8 * q := by exact_mod_cast hq
    linarith [hq']
  have hone : zeta8 ^ (8 * q : ℤ) = 1 := by
    rw [zpow_mul, zeta8_zpow_eight, one_zpow]
  calc zeta8 ^ m = zeta8 ^ ((v : ℤ) + 8 * q) := by rw [← hm]
    _ = zeta8 ^ (v : ℤ) * zeta8 ^ (8 * q : ℤ) :=
        zpow_add₀ (isPrimitiveRoot_zeta8.ne_zero (by norm_num)) _ _
    _ = zeta8 ^ (v : ℕ) := by rw [hone, mul_one, zpow_natCast]
    _ = charEight ((m : ZMod 8)) := by rw [charEight, hv]

theorem charLift_eighthPhase (n : α → ℤ) (w : α → ZMod 8) :
    charLift n (eighthPhase w) = ∏ a, charEight ((n a : ZMod 8) * w a) := by
  classical
  rw [charLift, charPhase_apply, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hpow : Complex.exp (2 * Real.pi * Complex.I * ((n a : ℤ) : ℂ) *
      ((eighthPhase w a : ℝ) : ℂ))
      = zeta8 ^ ((n a) * (((w a).val : ℕ) : ℤ)) := by
    rw [zeta8, ← Complex.exp_int_mul]
    congr 1
    rw [eighthPhase]
    push_cast
    field_simp
  rw [hpow, zeta8_zpow_eq_charEight]
  congr 1
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]


/-! ## The ensemble transfer -/

variable {Ω : Type*} [Fintype Ω]

/-- The support of an integer frequency vector. -/
def freqSupport (n : α → ℤ) : Finset α := Finset.univ.filter fun a => n a ≠ 0

theorem notMem_freqSupport_iff {n : α → ℤ} {a : α} : a ∉ freqSupport n ↔ n a = 0 := by
  simp [freqSupport]

/-- An ensemble of eighth-root residue vectors kills every nontrivial character of low support. -/
def EighthPhaseUniform (ev : Ω → (α → ZMod 8)) (K : ℕ) : Prop :=
  ∀ n : α → ℤ, (freqSupport n).card ≤ K → (∃ a, ((n a : ℤ) : ZMod 8) ≠ 0) →
    ∑ h : Ω, charLift n (eighthPhase (ev h)) = 0

/-- **Low-support uniformity of the coordinate tuples gives character vanishing.** -/
theorem eighthPhaseUniform_of_tupleUniform (ev : Ω → (α → ZMod 8)) (K : ℕ)
    (htuple : ∀ k : ℕ, k ≤ K → ∀ pts : Fin k → α, Function.Injective pts →
      ∀ w : Fin k → ZMod 8,
        ((Finset.univ.filter fun h : Ω => (fun i => ev h (pts i)) = w).card) * 8 ^ k
          = Fintype.card Ω) :
    EighthPhaseUniform ev K := by
  classical
  intro n hcard ⟨a₀, ha₀⟩
  obtain ⟨S, hSdef⟩ : ∃ S, S = freqSupport n := ⟨_, rfl⟩
  obtain ⟨pts, hptsdef⟩ : ∃ pts : Fin S.card → α,
      pts = fun i => ((S.equivFin.symm i : S) : α) := ⟨_, rfl⟩
  have hptsinj : Function.Injective pts := by
    intro i j hij
    rw [hptsdef] at hij
    exact S.equivFin.symm.injective (Subtype.ext hij)
  have hptsmem : ∀ i, pts i ∈ S := by
    intro i
    rw [hptsdef]
    exact (S.equivFin.symm i).2
  have hprod : ∀ h : Ω, charLift n (eighthPhase (ev h))
      = ∏ i : Fin S.card, charEight (((n (pts i) : ℤ) : ZMod 8) * ev h (pts i)) := by
    intro h
    rw [charLift_eighthPhase]
    have hrestrict : ∏ a, charEight (((n a : ℤ) : ZMod 8) * ev h a)
        = ∏ a ∈ S, charEight (((n a : ℤ) : ZMod 8) * ev h a) := by
      refine (Finset.prod_subset (Finset.subset_univ S) ?_).symm
      intro a _ haS
      rw [hSdef] at haS
      rw [notMem_freqSupport_iff.mp haS]
      simp [charEight]
    rw [hrestrict, ← Finset.prod_coe_sort S
      (fun a : α => charEight (((n a : ℤ) : ZMod 8) * ev h a))]
    refine (Equiv.prod_comp S.equivFin.symm
      (fun s : S => charEight (((n (s : α) : ℤ) : ZMod 8) * ev h (s : α)))).symm.trans ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hptsdef]
  have hunif : ∀ w : Fin S.card → ZMod 8,
      (Finset.univ.filter fun h : Ω => (fun i => ev h (pts i)) = w).card
        = (Finset.univ.filter fun h : Ω =>
            (fun i => ev h (pts i)) = (0 : Fin S.card → ZMod 8)).card := by
    intro w
    exact card_fiber_const_of_mul_eq (fun h i => ev h (pts i))
      (fun w' => htuple S.card (le_trans (le_of_eq (by rw [hSdef])) hcard) pts hptsinj w') w 0
  have ha₀S : a₀ ∈ S := by
    rw [hSdef, freqSupport, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hz
    rw [hz] at ha₀
    simp at ha₀
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin S.card, pts i₀ = a₀ := by
    refine ⟨S.equivFin ⟨a₀, ha₀S⟩, ?_⟩
    rw [hptsdef]
    simp
  rw [Finset.sum_congr rfl (fun h _ => hprod h)]
  exact sum_comp_prod_charEight_eq_zero (fun h i => ev h (pts i)) _ hunif
    ⟨i₀, by rw [hi₀]; exact ha₀⟩

/-- **The ensemble mean of a low-frequency trigonometric polynomial is its zero-frequency
coefficient** -- the same value as its Haar mean over the torus box. -/
theorem sum_trigLift_eighthPhase {ι : Type*} [DecidableEq ι] (ev : Ω → (α → ZMod 8)) {K : ℕ}
    (hunif : EighthPhaseUniform ev K)
    (P : Finset ι) (ν : ι → (α → ℤ)) (a : ι → ℂ)
    (hsupp : ∀ p ∈ P, (freqSupport (ν p)).card ≤ K)
    (hsmall : ∀ p ∈ P, ν p ≠ 0 → ∃ t, ((ν p t : ℤ) : ZMod 8) ≠ 0) :
    (∑ h : Ω, trigLift P ν a (eighthPhase (ev h)))
      = (Fintype.card Ω : ℂ) * freqBlock P ν a 0 := by
  classical
  have hswap : (∑ h : Ω, trigLift P ν a (eighthPhase (ev h)))
      = ∑ p ∈ P, a p * ∑ h : Ω, charLift (ν p) (eighthPhase (ev h)) := by
    simp only [trigLift]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  have hterm : ∀ p ∈ P, a p * ∑ h : Ω, charLift (ν p) (eighthPhase (ev h))
      = if ν p = 0 then (Fintype.card Ω : ℂ) * a p else 0 := by
    intro p hp
    by_cases hz : ν p = 0
    · rw [if_pos hz]
      have hone : ∀ h : Ω, charLift (ν p) (eighthPhase (ev h)) = 1 := by
        intro h
        rw [hz, charLift_zero_index]
      rw [Finset.sum_congr rfl (fun h _ => hone h), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    · rw [if_neg hz, hunif (ν p) (hsupp p hp) (hsmall p hp hz), mul_zero]
  rw [Finset.sum_congr rfl hterm, freqBlock, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hz : ν p = 0 <;> simp [hz]

/-- **The ensemble mean equals the Haar mean.**  A low-frequency trigonometric polynomial has the
same average over the eighth-root ensemble as over the torus box. -/
theorem average_trigLift_eighthPhase_eq_integral_box {ι : Type*} [DecidableEq ι]
    [Nonempty Ω] (ev : Ω → (α → ZMod 8)) {K : ℕ} (hunif : EighthPhaseUniform ev K)
    (P : Finset ι) (ν : ι → (α → ℤ)) (a : ι → ℂ)
    (hsupp : ∀ p ∈ P, (freqSupport (ν p)).card ≤ K)
    (hsmall : ∀ p ∈ P, ν p ≠ 0 → ∃ t, ((ν p t : ℤ) : ZMod 8) ≠ 0) :
    ((Fintype.card Ω : ℂ))⁻¹ * ∑ h : Ω, trigLift P ν a (eighthPhase (ev h))
      = ∫ x in torusBox α, trigLift P ν a x := by
  have hne : ((Fintype.card Ω : ℂ)) ≠ 0 := by
    have : 0 < Fintype.card Ω := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [sum_trigLift_eighthPhase ev hunif P ν a hsupp hsmall,
    integral_box_trigLift_eq_freqBlock_zero, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GaloisForLFunctions.HTGeometry

end
