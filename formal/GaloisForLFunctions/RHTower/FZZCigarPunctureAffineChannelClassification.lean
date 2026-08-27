import GaloisForLFunctions.RHTower.FZZCigarPunctureBoxRankOneNoGo

/-!
# Exact finite affine-channel classification at FZZ puncture

The regular rank-one no-go exposes one required node at embedded target energy. This file solves
the full finite affine-channel local problem. Each channel has on-shell coefficient `cᵢ`, slope
`dᵢ`, and incidence amplitude `aᵢ`. Their complete continuum source factors as

`(C + (x-E)D) 1_(E,E+1)`,

where `C=Σ aᵢcᵢ` and `D=Σ aᵢdᵢ`.

There is a nonzero `L²` embedded mode exactly when `C=0` and `D≠0`. In that case state is unique
almost everywhere and equals `-D 1_(E,E+1)`. Thus finite channel mixing does not evade pole wall:
it replaces componentwise node by one exact collective on-shell cancellation and demands a
nonzero transverse jet.

This is both survivor and warning. Signed/complex finite channels can manufacture a local mode
whenever collective node is supplied, so local occurrence alone cannot select zeta ordinates. FZZ
producer must derive `C(E)=0` coefficient-faithfully from winding-condensate dynamics, while
retaining `D(E)≠0`, without fitting either to Xi zeros.

`[NEW] [CLASSIFICATION] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex MeasureTheory Set
open scoped ENNReal BigOperators

namespace RHTower

noncomputable section

/-- One affine continuum channel near target energy. -/
def fzzPunctureAffineChannelFormFactor
    (E : ℝ) (c d : ℂ) (x : ℝ) : ℂ :=
  (c + ((x - E : ℝ) : ℂ) * d) * fzzPunctureBoxFormFactor E x

/-- Collective on-shell source coefficient. -/
def fzzPunctureAffineCollectiveOnShell {k : ℕ}
    (a c : Fin k → ℂ) : ℂ :=
  ∑ i, a i * c i

/-- Collective first transverse source jet. -/
def fzzPunctureAffineCollectiveSlope {k : ℕ}
    (a d : Fin k → ℂ) : ℂ :=
  ∑ i, a i * d i

/-- Exact finite-channel factorization into collective value and slope. -/
theorem fzzPunctureAffineChannel_sum_factorization {k : ℕ}
    (E : ℝ) (a c d : Fin k → ℂ) (x : ℝ) :
    ∑ i, a i * fzzPunctureAffineChannelFormFactor E (c i) (d i) x =
      (fzzPunctureAffineCollectiveOnShell a c +
        ((x - E : ℝ) : ℂ) * fzzPunctureAffineCollectiveSlope a d) *
          fzzPunctureBoxFormFactor E x := by
  let t : ℂ := ((x - E : ℝ) : ℂ)
  let b : ℂ := fzzPunctureBoxFormFactor E x
  calc
    ∑ i, a i * fzzPunctureAffineChannelFormFactor E (c i) (d i) x =
        ∑ i, (a i * c i * b + (t * (a i * d i)) * b) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [fzzPunctureAffineChannelFormFactor, t, b]
          ring
    _ = (∑ i, a i * c i) * b + (∑ i, t * (a i * d i)) * b := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ = (fzzPunctureAffineCollectiveOnShell a c +
          t * fzzPunctureAffineCollectiveSlope a d) * b := by
      rw [← Finset.mul_sum]
      simp only [fzzPunctureAffineCollectiveOnShell,
        fzzPunctureAffineCollectiveSlope]
      ring
    _ = _ := rfl

/-- Finite affine-channel continuum eigen-equation. -/
def fzzPunctureAffineChannelEigenEquation {k : ℕ}
    (E : ℝ) (a c d : Fin k → ℂ) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 volume ∧
    ∀ᵐ x : ℝ ∂volume,
      (((x - E : ℝ) : ℂ) * f x) +
        (fzzPunctureAffineCollectiveOnShell a c +
          ((x - E : ℝ) : ℂ) * fzzPunctureAffineCollectiveSlope a d) *
            fzzPunctureBoxFormFactor E x = 0

/-- Every solution forces collective node and has unique surviving state. -/
theorem fzzPunctureAffineChannelEigenEquation_classification {k : ℕ}
    (E : ℝ) (a c d : Fin k → ℂ) (f : ℝ → ℂ)
    (h : fzzPunctureAffineChannelEigenEquation E a c d f) :
    fzzPunctureAffineCollectiveOnShell a c = 0 ∧
      f =ᵐ[volume] fun x =>
        -fzzPunctureAffineCollectiveSlope a d * fzzPunctureBoxFormFactor E x := by
  let C := fzzPunctureAffineCollectiveOnShell a c
  let D := fzzPunctureAffineCollectiveSlope a d
  let g : ℝ → ℂ := fun x => f x + D * fzzPunctureBoxFormFactor E x
  have hgmem : MemLp g 2 volume := by
    exact h.1.add ((fzzPunctureBoxFormFactor_memLp E).const_mul D)
  have hgeq : fzzPunctureBoxRankOneEigenEquation E C g := by
    refine ⟨hgmem, ?_⟩
    filter_upwards [h.2] with x hx
    dsimp [g, C, D]
    linear_combination hx
  have hclass := fzzPunctureBoxRankOneEigenEquation_classification E C g hgeq
  refine ⟨hclass.1, ?_⟩
  filter_upwards [hclass.2] with x hx
  dsimp [g, D] at hx
  linear_combination hx

/-- Existence of a nonzero embedded affine-channel point mode. -/
def FZZPunctureAffineChannelPointMode {k : ℕ}
    (E : ℝ) (a c d : Fin k → ℂ) : Prop :=
  ∃ f : ℝ → ℂ,
    fzzPunctureAffineChannelEigenEquation E a c d f ∧
      ¬ f =ᵐ[volume] (0 : ℝ → ℂ)

/-- Exact finite-channel occurrence law: collective node plus nonzero transverse jet. -/
theorem fzzPunctureAffineChannelPointMode_iff {k : ℕ}
    (E : ℝ) (a c d : Fin k → ℂ) :
    FZZPunctureAffineChannelPointMode E a c d ↔
      fzzPunctureAffineCollectiveOnShell a c = 0 ∧
        fzzPunctureAffineCollectiveSlope a d ≠ 0 := by
  constructor
  · rintro ⟨f, heq, hf⟩
    have hclass := fzzPunctureAffineChannelEigenEquation_classification E a c d f heq
    refine ⟨hclass.1, ?_⟩
    intro hD
    apply hf
    filter_upwards [hclass.2] with x hx
    rw [hx, hD]
    simp
  · rintro ⟨hC, hD⟩
    let D := fzzPunctureAffineCollectiveSlope a d
    let f : ℝ → ℂ := fun x => -D * fzzPunctureBoxFormFactor E x
    have hfmem : MemLp f 2 volume :=
      (fzzPunctureBoxFormFactor_memLp E).const_mul (-D)
    have heq : fzzPunctureAffineChannelEigenEquation E a c d f := by
      refine ⟨hfmem, Filter.Eventually.of_forall ?_⟩
      intro x
      dsimp [f, D]
      rw [hC]
      ring
    refine ⟨f, heq, ?_⟩
    intro hfzero
    apply fzzPunctureNodalBoxFormalState_ne_ae_zero E
    filter_upwards [hfzero] with x hx
    dsimp [f, D] at hx
    change fzzPunctureNodalBoxFormalState E x = 0
    have hD' : fzzPunctureAffineCollectiveSlope a d ≠ 0 := hD
    have hmul : fzzPunctureAffineCollectiveSlope a d *
        fzzPunctureNodalBoxFormalState E x = 0 := by
      simpa [fzzPunctureNodalBoxFormalState] using hx
    exact (mul_eq_zero.mp hmul).resolve_left hD'

/-- Unit nodal channel realizes the positive side of classification at every target energy. -/
theorem fzzPunctureUnitNodalAffineChannelPointMode (E : ℝ) :
    FZZPunctureAffineChannelPointMode E
      (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => (0 : ℂ))
      (fun _ : Fin 1 => (1 : ℂ)) := by
  rw [fzzPunctureAffineChannelPointMode_iff]
  simp [fzzPunctureAffineCollectiveOnShell, fzzPunctureAffineCollectiveSlope]

/-- Unit regular channel cannot realize point mode, regardless of its slope. -/
theorem not_fzzPunctureUnitRegularAffineChannelPointMode (E : ℝ) (d : Fin 1 → ℂ) :
    ¬ FZZPunctureAffineChannelPointMode E
      (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => (1 : ℂ)) d := by
  rw [fzzPunctureAffineChannelPointMode_iff]
  simp [fzzPunctureAffineCollectiveOnShell]

end

end RHTower
