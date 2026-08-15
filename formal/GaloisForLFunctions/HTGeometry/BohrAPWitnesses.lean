import GaloisForLFunctions.HTGeometry.AlmostPeriodicHull
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Realizations of Bohr almost periodicity

Bochner's criterion is realized by constants, by every character `s ↦ exp (i λ s)` — whose
translation orbit is the unimodular circle through it — and, since relative compactness of orbits is
stable under scalars and sums, by every trigonometric polynomial.  This makes the return-time and
hull theorems of the almost-periodic layer available on an explicit nonconstant family.
-/

open BoundedContinuousFunction Metric
open scoped Pointwise

namespace GaloisForLFunctions

noncomputable section

/-! ## Constants -/

theorem bcfTranslate_const (t : ℝ) (c : ℂ) :
    bcfTranslate t (BoundedContinuousFunction.const ℝ c) =
      BoundedContinuousFunction.const ℝ c := by
  ext s
  simp

theorem bcfOrbit_const (c : ℂ) :
    bcfOrbit (BoundedContinuousFunction.const ℝ c) =
      {BoundedContinuousFunction.const ℝ c} := by
  ext g
  simp only [bcfOrbit, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht⟩
    rw [← ht, bcfTranslate_const]
  · rintro rfl
    exact ⟨0, bcfTranslate_zero _⟩

theorem isBohrAP_const (c : ℂ) :
    IsBohrAP (BoundedContinuousFunction.const ℝ c) := by
  unfold IsBohrAP
  rw [bcfOrbit_const, closure_singleton]
  exact isCompact_singleton

/-! ## Stability -/

/-- Relative compactness of orbits is stable under scalars. -/
theorem IsBohrAP.smul {f : ℝ →ᵇ ℂ} (hf : IsBohrAP f) (c : ℂ) :
    IsBohrAP (c • f) := by
  have hsmul : ∀ t : ℝ, bcfTranslate t (c • f) = c • bcfTranslate t f := by
    intro t
    ext s
    simp
  have himage : bcfOrbit (c • f) = (fun g : ℝ →ᵇ ℂ => c • g) '' bcfOrbit f := by
    ext g
    simp only [bcfOrbit, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨bcfTranslate t f, ⟨t, rfl⟩, by rw [← ht, hsmul t]⟩
    · rintro ⟨h, ⟨t, ht⟩, hgh⟩
      exact ⟨t, by rw [hsmul t, ht, hgh]⟩
  have hcont : Continuous fun g : ℝ →ᵇ ℂ => c • g := continuous_const_smul c
  have hcompact : IsCompact ((fun g : ℝ →ᵇ ℂ => c • g) '' closure (bcfOrbit f)) :=
    hf.image hcont
  refine hcompact.of_isClosed_subset isClosed_closure ?_
  rw [himage]
  exact closure_minimal (Set.image_mono subset_closure) hcompact.isClosed

/-- Relative compactness of orbits is stable under sums. -/
theorem IsBohrAP.add {f g : ℝ →ᵇ ℂ} (hf : IsBohrAP f) (hg : IsBohrAP g) :
    IsBohrAP (f + g) := by
  have hadd : ∀ t : ℝ, bcfTranslate t (f + g) = bcfTranslate t f + bcfTranslate t g := by
    intro t
    ext s
    simp
  have hcf : IsCompact (closure (bcfOrbit f)) := hf
  have hcg : IsCompact (closure (bcfOrbit g)) := hg
  have hcompact : IsCompact (closure (bcfOrbit f) + closure (bcfOrbit g)) :=
    IsCompact.add hcf hcg
  refine hcompact.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hcompact.isClosed
  rintro h ⟨t, ht⟩
  refine ⟨bcfTranslate t f, subset_closure ⟨t, rfl⟩,
    bcfTranslate t g, subset_closure ⟨t, rfl⟩, ?_⟩
  show bcfTranslate t f + bcfTranslate t g = h
  rw [← hadd t]
  exact ht

/-! ## Characters -/

/-- The unimodular character `s ↦ exp (i λ s)` as a bounded continuous function. -/
def bcfChar (lam : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s : ℝ => Complex.exp ((lam * s : ℝ) * Complex.I))
    (by fun_prop) 1
    (fun s => le_of_eq (Complex.norm_exp_ofReal_mul_I (lam * s)))

@[simp]
theorem bcfChar_apply (lam s : ℝ) :
    bcfChar lam s = Complex.exp ((lam * s : ℝ) * Complex.I) := rfl

theorem norm_bcfChar_apply (lam s : ℝ) : ‖bcfChar lam s‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (lam * s)

/-- Translating a character multiplies it by a unimodular constant. -/
theorem bcfTranslate_bcfChar (lam t : ℝ) :
    bcfTranslate t (bcfChar lam) =
      Complex.exp ((lam * t : ℝ) * Complex.I) • bcfChar lam := by
  ext s
  rw [bcfTranslate_apply, bcfChar_apply, BoundedContinuousFunction.smul_apply,
    bcfChar_apply, smul_eq_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Characters are Bohr almost periodic.**  The orbit lies on the unimodular circle through the
character, which is compact. -/
theorem isBohrAP_bcfChar (lam : ℝ) : IsBohrAP (bcfChar lam) := by
  have hcont : Continuous fun c : ℂ => c • bcfChar lam := by fun_prop
  have hcompact : IsCompact ((fun c : ℂ => c • bcfChar lam) '' Metric.sphere 0 1) :=
    (isCompact_sphere 0 1).image hcont
  refine hcompact.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hcompact.isClosed
  rintro h ⟨t, ht⟩
  refine ⟨Complex.exp ((lam * t : ℝ) * Complex.I), ?_, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right,
      Complex.norm_exp_ofReal_mul_I (lam * t)]
  · show Complex.exp ((lam * t : ℝ) * Complex.I) • bcfChar lam = h
    rw [← bcfTranslate_bcfChar]
    exact ht

/-! ## Trigonometric polynomials -/

/-- **Trigonometric polynomials are Bohr almost periodic.** -/
theorem isBohrAP_trigPoly {n : ℕ} (a : Fin n → ℂ) (lam : Fin n → ℝ) :
    IsBohrAP (∑ i, a i • bcfChar (lam i)) := by
  classical
  induction n with
  | zero =>
      have hzero : (∑ i : Fin 0, a i • bcfChar (lam i)) =
          BoundedContinuousFunction.const ℝ 0 := by
        ext s
        simp
      rw [hzero]
      exact isBohrAP_const 0
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      exact (ih (fun i => a i.castSucc) (fun i => lam i.castSucc)).add
        ((isBohrAP_bcfChar (lam (Fin.last n))).smul (a (Fin.last n)))

/-- The unit-frequency character has compact translation orbit. -/
theorem isBohrAP_bcfChar_one : IsBohrAP (bcfChar 1) :=
  isBohrAP_bcfChar 1

end

end GaloisForLFunctions
