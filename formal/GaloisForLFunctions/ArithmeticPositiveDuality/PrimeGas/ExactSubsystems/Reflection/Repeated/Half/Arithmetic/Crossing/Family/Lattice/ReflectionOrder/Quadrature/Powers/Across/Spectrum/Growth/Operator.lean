import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum.Growth.Rate
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier

/-! # Elementary reciprocal readings as bounded Hilbert-space observables -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum.Growth

open Real

abbrev Tail (N : ℕ) := {p : Nat.Primes // N < p.val}
abbrev Sector (N : ℕ) := lp (fun _ : Tail N => ℂ) 2

/-- Signed entry of the elementary observation after power normalization. -/
def entry {N : ℕ} (s : ℂ) (β : ℝ) (p : Tail N) : ℂ :=
  ((reading p.val 1 s / (p.val.val : ℝ)^β : ℝ) : ℂ)

private theorem norm_entry {N : ℕ} (s : ℂ) (β : ℝ) (p : Tail N) :
    ‖entry s β p‖=adjusted s β p.val := by
  have pos := rpow_pos_of_pos (Nat.cast_pos.mpr p.val.property.pos : (0 : ℝ)<p.val.val) β
  rw [entry,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos pos,adjusted]

/-- Bounded realization means that a continuous linear operator has
the measured entries on all elementary unit coordinate vectors. -/
def Realized (N : ℕ) (s : ℂ) (β : ℝ) : Prop :=
  ∃ T : Sector N →L[ℂ] Sector N, ∀ p : Tail N,
    T (lp.single 2 p (1 : ℂ))=lp.single 2 p (entry s β p)

theorem realization_iff (N : ℕ) (s : ℂ) (β : ℝ) :
    Realized N s β ↔ s.re=1/2 ∨ displacement s ≤ β := by
  rw [←rate_iff s N β]
  constructor
  · rintro ⟨T,action⟩
    refine ⟨‖T‖,fun p hp => ?_⟩
    let q : Tail N := ⟨p,hp⟩
    have h := T.le_opNorm (lp.single 2 q (1 : ℂ))
    simpa only [action q,lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one,mul_one,
      norm_entry] using h
  · rintro ⟨C,bound⟩
    have norm_bound (p : Tail N) : ‖entry s β p‖ ≤ max C 0 :=
      (norm_entry s β p).trans_le ((bound p.val p.property).trans (le_max_left _ _))
    exact ⟨_root_.GaloisForLFunctions.lpDiagonalCLM (entry s β) (le_max_right C 0) norm_bound,
      _root_.GaloisForLFunctions.lpDiagonalCLM_single (entry s β) (le_max_right C 0) norm_bound⟩

/-- A bounded operator realizing the raw signed observations on any
prime tail exists exactly when divisor splitting preserves norm. -/
theorem raw_operator_isometry (N : ℕ) (s : ℂ) :
    Realized N s 0 ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  rw [realization_iff,displacement,abs_nonpos_iff,sub_eq_zero,or_self,split_isometric_iff]

/-- RH asks whether each strip zero admits a bounded operator with
the measured elementary entries on a prescribed prime tail. -/
theorem rh_iff_bounded_at_zeros (N : ℕ) :
    RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val=0 → Realized N s.val 0 := by
  rw [rh_iff_trace_zero_forces_isometry]
  constructor
  · intro h s zero
    exact (raw_operator_isometry N s.val).mpr (h s ((adjacentTrace_zero_iff s).mpr zero))
  · intro h s zero
    exact (raw_operator_isometry N s.val).mp (h s ((adjacentTrace_zero_iff s).mp zero))

#print axioms realization_iff
#print axioms raw_operator_isometry
#print axioms rh_iff_bounded_at_zeros

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum.Growth
