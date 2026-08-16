import GaloisForLFunctions.RHTower.MobiusReciprocalAllocationJacobian

/-!
# The stretched column bound of the reciprocal allocation kernel

The reciprocal-allocation kernel puts weight `1/(H(n)·T(ρ)·N(n,ρ))` on each labelled edge.  A
square-root forward token law `N(n,ρ) ≥ √(n/(aT(ρ)))/K₁` turns that weight into the critical
square-root form

`1/(H(n)T(ρ)N(n,ρ)) ≤ K₁√a/(√n·√T(ρ))`,

in which the reservoir product appears only through `√T`.  Inverting the token interval produces at
most `K₂√(vT/a)` anchors per structural assignment, and those two square roots cancel exactly: one
structural class contributes at most `K₁K₂√(v/n)`.  Summing over the structural assignments bounds
the whole column load by the product of the two stretched constants with the number of structures —
no dependence on the reservoir magnitude survives.
-/

namespace RHTower

open Finset

namespace ReciprocalAllocationSystem

variable {Anchor Allocation Target : Type*}
  [Fintype Anchor] [Fintype Target] [DecidableEq Target]

/-- **The critical square-root edge weight.**  A square-root forward token law turns one
reciprocal-allocation edge weight into a weight in which the reservoir product appears only through
`√T`. -/
theorem edge_weight_le {H T N size a K₁ : ℝ} (hH : 1 ≤ H) (hT : 0 < T) (hN : 0 < N)
    (ha : 0 < a) (hsize : 0 < size) (hK₁ : 0 < K₁)
    (hforward : Real.sqrt (size / (a * T)) ≤ K₁ * N) :
    1 / (H * T * N) ≤ K₁ * Real.sqrt a / (Real.sqrt size * Real.sqrt T) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hsq : Real.sqrt (size / (a * T)) = Real.sqrt size / (Real.sqrt a * Real.sqrt T) := by
    rw [Real.sqrt_div' size (by positivity), Real.sqrt_mul ha.le]
  rw [hsq] at hforward
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hst : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hss : 0 < Real.sqrt size := Real.sqrt_pos.2 hsize
  have hTsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
  have hf : Real.sqrt size ≤ K₁ * N * (Real.sqrt a * Real.sqrt T) := by
    rw [div_le_iff₀ (by positivity)] at hforward
    exact hforward
  have hchain : Real.sqrt size * Real.sqrt T ≤ K₁ * Real.sqrt a * (H * T * N) := by
    calc Real.sqrt size * Real.sqrt T
        ≤ K₁ * N * (Real.sqrt a * Real.sqrt T) * Real.sqrt T :=
          mul_le_mul_of_nonneg_right hf hst.le
      _ = K₁ * Real.sqrt a * (T * N) := by
          linear_combination (K₁ * N * Real.sqrt a) * hTsq
      _ ≤ K₁ * Real.sqrt a * (H * T * N) := by
          have h1 : T * N ≤ H * T * N := by nlinarith [mul_pos hT hN]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact hchain

/-- The set of labelled incoming edges at one physical terminal. -/
noncomputable def incoming (A : ReciprocalAllocationSystem Anchor Allocation Target)
    (v : Target) : Finset ((_ : Anchor) × Allocation) := by
  classical
  exact Finset.univ.sigma fun n : Anchor => (A.admissible n).filter fun ρ => v ∈ A.terminals n ρ

theorem mem_incoming (A : ReciprocalAllocationSystem Anchor Allocation Target)
    (v : Target) (p : (_ : Anchor) × Allocation) :
    p ∈ A.incoming v ↔ p.2 ∈ A.admissible p.1 ∧ v ∈ A.terminals p.1 p.2 := by
  classical
  simp [incoming, Finset.mem_sigma, Finset.mem_filter]

/-- The column load is the sum of the labelled edge weights. -/
theorem sum_harmonicKernel_eq_incoming
    (A : ReciprocalAllocationSystem Anchor Allocation Target) (v : Target) :
    ∑ n : Anchor, A.harmonicKernel n v
      = ∑ p ∈ A.incoming v,
          1 / (A.harmonicNormalizer p.1 * A.scale p.2 * A.terminalCount p.1 p.2) := by
  classical
  have hsplit : ∀ n : Anchor, A.harmonicKernel n v
      = ∑ ρ ∈ (A.admissible n).filter fun ρ => v ∈ A.terminals n ρ,
          1 / (A.harmonicNormalizer n * A.scale ρ * A.terminalCount n ρ) := by
    intro n
    rw [harmonicKernel, Finset.sum_filter]
  simp only [hsplit]
  rw [Finset.sum_sigma']
  rfl

set_option maxHeartbeats 1000000 in
/-- **(4) The stretched column bound.**  With the normalizer bound `H ≥ 1`, the square-root forward
token law, the co-moving law, a structural classification of the incoming edges in which each class
carries one reservoir product, and an inverse-interval count `K₂√(vT/a)` per class, the
reciprocal-allocation column load is at most `K₁K₂√ratio` times the number of structural classes.
No dependence on the reservoir magnitude survives. -/
theorem column_load_le {Str : Type*} [Fintype Str] [DecidableEq Str]
    (A : ReciprocalAllocationSystem Anchor Allocation Target)
    (v : Target) (σ : ((_ : Anchor) × Allocation) → Str)
    (size : Anchor → ℝ) (targetSize a K₁ K₂ ratio : ℝ)
    (ha : 0 < a) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hratio : 0 < ratio)
    (htarget : 0 < targetSize)
    (hsize : ∀ n, 0 < size n)
    (hH : ∀ n, 1 ≤ A.harmonicNormalizer n)
    (hcomove : ∀ n, targetSize ≤ ratio * size n)
    (hforward : ∀ p ∈ A.incoming v,
      Real.sqrt (size p.1 / (a * A.scale p.2)) ≤ K₁ * A.terminalCount p.1 p.2)
    (hscale : ∀ s : Str, ∀ p ∈ (A.incoming v).filter fun q => σ q = s,
      ∀ q ∈ (A.incoming v).filter fun q => σ q = s, A.scale p.2 = A.scale q.2)
    (hclass : ∀ s : Str, ∀ p ∈ (A.incoming v).filter fun q => σ q = s,
      (((A.incoming v).filter fun q => σ q = s).card : ℝ)
        ≤ K₂ * Real.sqrt (targetSize * A.scale p.2 / a)) :
    ∑ n : Anchor, A.harmonicKernel n v
      ≤ (Fintype.card Str : ℝ) * (K₁ * K₂ * Real.sqrt ratio) := by
  classical
  rw [A.sum_harmonicKernel_eq_incoming v]
  have hts : 0 < Real.sqrt targetSize := Real.sqrt_pos.2 htarget
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hr : 0 < Real.sqrt ratio := Real.sqrt_pos.2 hratio
  have hedge : ∀ p ∈ A.incoming v,
      1 / (A.harmonicNormalizer p.1 * A.scale p.2 * A.terminalCount p.1 p.2)
        ≤ K₁ * Real.sqrt a * Real.sqrt ratio
            / (Real.sqrt targetSize * Real.sqrt (A.scale p.2)) := by
    intro p hp
    have hp' := (A.mem_incoming v p).1 hp
    have hcount : 0 < (A.terminalCount p.1 p.2 : ℝ) := by
      exact_mod_cast Finset.card_pos.2 (A.terminals_nonempty p.1 p.2 hp'.1)
    have hbase := edge_weight_le (hH p.1) (A.scale_pos p.2) hcount ha (hsize p.1) hK₁
      (hforward p hp)
    refine le_trans hbase ?_
    have hsz : Real.sqrt targetSize ≤ Real.sqrt ratio * Real.sqrt (size p.1) := by
      rw [← Real.sqrt_mul hratio.le]
      exact Real.sqrt_le_sqrt (hcomove p.1)
    have hss : 0 < Real.sqrt (size p.1) := Real.sqrt_pos.2 (hsize p.1)
    have hst : 0 < Real.sqrt (A.scale p.2) := Real.sqrt_pos.2 (A.scale_pos p.2)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hkey : Real.sqrt targetSize * Real.sqrt (A.scale p.2)
        ≤ Real.sqrt ratio * Real.sqrt (size p.1) * Real.sqrt (A.scale p.2) :=
      mul_le_mul_of_nonneg_right hsz hst.le
    calc K₁ * Real.sqrt a * (Real.sqrt targetSize * Real.sqrt (A.scale p.2))
        ≤ K₁ * Real.sqrt a
            * (Real.sqrt ratio * Real.sqrt (size p.1) * Real.sqrt (A.scale p.2)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = K₁ * Real.sqrt a * Real.sqrt ratio
            * (Real.sqrt (size p.1) * Real.sqrt (A.scale p.2)) := by ring
  refine le_trans (Finset.sum_le_sum hedge) ?_
  have hclasses : ∑ p ∈ A.incoming v,
      K₁ * Real.sqrt a * Real.sqrt ratio
        / (Real.sqrt targetSize * Real.sqrt (A.scale p.2))
      = ∑ s : Str, ∑ p ∈ (A.incoming v).filter fun q => σ q = s,
          K₁ * Real.sqrt a * Real.sqrt ratio
            / (Real.sqrt targetSize * Real.sqrt (A.scale p.2)) :=
    (Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_univ (σ p)) _).symm
  rw [hclasses]
  have hbound : ∀ s : Str,
      ∑ p ∈ (A.incoming v).filter fun q => σ q = s,
        K₁ * Real.sqrt a * Real.sqrt ratio
          / (Real.sqrt targetSize * Real.sqrt (A.scale p.2))
        ≤ K₁ * K₂ * Real.sqrt ratio := by
    intro s
    rcases Finset.eq_empty_or_nonempty ((A.incoming v).filter fun q => σ q = s) with hempty | hne
    · rw [hempty, Finset.sum_empty]
      positivity
    · obtain ⟨p₀, hp₀⟩ := hne
      have hconst : ∀ p ∈ (A.incoming v).filter fun q => σ q = s,
          K₁ * Real.sqrt a * Real.sqrt ratio
              / (Real.sqrt targetSize * Real.sqrt (A.scale p.2))
            = K₁ * Real.sqrt a * Real.sqrt ratio
              / (Real.sqrt targetSize * Real.sqrt (A.scale p₀.2)) := by
        intro p hp
        rw [hscale s p hp p₀ hp₀]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard₀ := hclass s p₀ hp₀
      have hst₀ : 0 < Real.sqrt (A.scale p₀.2) := Real.sqrt_pos.2 (A.scale_pos p₀.2)
      have hexp : Real.sqrt (targetSize * A.scale p₀.2 / a)
          = Real.sqrt targetSize * Real.sqrt (A.scale p₀.2) / Real.sqrt a := by
        rw [Real.sqrt_div' (targetSize * A.scale p₀.2) ha.le, Real.sqrt_mul htarget.le]
      rw [hexp] at hcard₀
      have hfin : (((A.incoming v).filter fun q => σ q = s).card : ℝ)
          * (K₁ * Real.sqrt a * Real.sqrt ratio
              / (Real.sqrt targetSize * Real.sqrt (A.scale p₀.2)))
          ≤ (K₂ * (Real.sqrt targetSize * Real.sqrt (A.scale p₀.2) / Real.sqrt a))
            * (K₁ * Real.sqrt a * Real.sqrt ratio
              / (Real.sqrt targetSize * Real.sqrt (A.scale p₀.2))) := by
        apply mul_le_mul_of_nonneg_right hcard₀
        positivity
      refine le_trans hfin (le_of_eq ?_)
      field_simp
  refine le_trans (Finset.sum_le_sum fun s _ => hbound s) ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

end ReciprocalAllocationSystem

end RHTower
