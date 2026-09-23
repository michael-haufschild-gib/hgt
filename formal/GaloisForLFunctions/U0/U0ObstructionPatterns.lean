/-
# Obstruction patterns: closed-form regions where the filled Julia set meets the unit disk

The complex generalization of `U0WindowObstruction` — the real-interval obstruction becomes two
explicit REGIONS of parameters, with no real-order arguments anywhere:

* **P1 (fixed-point pattern).**  For any square root `s` of `1 − 4b` and `β = (1+s)/2` (a fixed
  point of `z ↦ z² + b`), the point `x₀ = √(−β−b)` has the finite orbit `x₀ ↦ −β ↦ β ↦ β`,
  and `‖x₀‖ ≤ 1 ⟺ ‖β + b‖ ≤ 1`.  Obstructed region: `min± ‖(1±s)/2 + b‖ ≤ 1` — in the
  `s`-coordinate `b = (1−s²)/4` this is the exact rational condition `|s−3|²·|s+1|² ≤ 16`.

* **P2 (2-cycle pattern).**  For any root `γ` of `γ² + γ + b + 1 = 0` (a 2-cycle point, with
  partner `γ' = −1−γ`), the point `x = √(γ−b)` satisfies `x² + b = γ`, so its orbit is
  `x ↦ γ ↦ γ' ↦ γ ↦ …` — finite; obstructed when `‖γ − b‖ ≤ 1`.

Together with deeper preperiodic patterns these regions carve the obstructed lobes of the
parameter ring `2 < ‖b‖ ≤ 2+√2` mapped in `computations/rho_curve_recon/` — the complement of
the viability set `𝒱 = {b : K_b ∩ D̄(0,1) = ∅}` whose boundary is the critical curve `ρ(arg b)`.
-/
import GaloisForLFunctions.Bottcher.Dynamics
import Mathlib.Analysis.Complex.Polynomial.Basic

open Complex Set Bottcher

namespace U0ObstructionPatterns

/-- Shared endgame: a point of modulus `≤ 1` whose orbit lies in a three-point set is an
obstruction witness. -/
theorem mem_filledJulia_of_orbit_three {b x p q : ℂ}
    (h1 : quadratic b x = p) (h2 : quadratic b p = q) (h3 : quadratic b q = q) :
    x ∈ filledJulia b := by
  have horbit : ∀ n : ℕ, (quadratic b)^[n] x ∈ ({x, p, q} : Set ℂ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
      rcases ih with h | h | h
      · rw [h, h1]; tauto
      · rw [h, h2]; tauto
      · rw [h, h3]; tauto
  rw [mem_filledJulia_iff]
  have hfin : ({x, p, q} : Set ℂ).Finite := Set.toFinite _
  refine hfin.isBounded.subset ?_
  rw [Set.range_subset_iff]
  exact horbit

/-- Modulus of a square root: `x² = w` and `‖w‖ ≤ 1` give `‖x‖ ≤ 1`. -/
theorem norm_le_one_of_sq {x w : ℂ} (hx : x ^ (2 : ℕ) = w) (hw : ‖w‖ ≤ 1) : ‖x‖ ≤ 1 := by
  have h2 : ‖x‖ ^ (2 : ℕ) = ‖w‖ := by rw [← norm_pow, hx]
  nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]

/-- **P1 — the fixed-point obstruction pattern.**  For any square root `s` of `1−4b` with
`‖(1+s)/2 + b‖ ≤ 1`, the filled Julia set meets the closed unit disk. -/
theorem filledJulia_meets_unit_disk_P1 {b s : ℂ} (hs : s ^ (2 : ℕ) = 1 - 4 * b)
    (hcond : ‖(1 + s) / 2 + b‖ ≤ 1) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia b := by
  set β : ℂ := (1 + s) / 2 with hβ
  have hβfix : β ^ (2 : ℕ) + b = β := by
    rw [hβ]
    linear_combination hs / 4
  obtain ⟨x₀, hx₀⟩ : ∃ x : ℂ, x ^ (2 : ℕ) = -β - b :=
    IsAlgClosed.exists_pow_nat_eq (-β - b) (by norm_num : 0 < 2)
  refine ⟨x₀, ?_, ?_⟩
  · refine norm_le_one_of_sq hx₀ ?_
    rw [show -β - b = -(β + b) from by ring, norm_neg]
    exact hcond
  · refine mem_filledJulia_of_orbit_three (p := -β) (q := β) ?_ ?_ ?_
    · show x₀ ^ (2 : ℕ) + b = -β
      rw [hx₀]; ring
    · show (-β) ^ (2 : ℕ) + b = β
      calc (-β) ^ (2 : ℕ) + b = β ^ (2 : ℕ) + b := by ring
        _ = β := hβfix
    · show β ^ (2 : ℕ) + b = β
      exact hβfix

/-- **P2 — the 2-cycle obstruction pattern.**  For any root `γ` of the 2-cycle equation
`γ² + γ + b + 1 = 0` with `‖γ − b‖ ≤ 1`, the filled Julia set meets the closed unit disk.
(The 2-cycle is `{γ, −1−γ}`; the witness is a square root of `γ − b`, one step before it.) -/
theorem filledJulia_meets_unit_disk_P2 {b γ : ℂ} (hγ : γ ^ (2 : ℕ) + γ + b + 1 = 0)
    (hcond : ‖γ - b‖ ≤ 1) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia b := by
  set γ' : ℂ := -1 - γ with hγ'
  have h1 : quadratic b γ = γ' := by
    show γ ^ (2 : ℕ) + b = γ'
    rw [hγ']
    linear_combination hγ
  have h2 : quadratic b γ' = γ := by
    show γ' ^ (2 : ℕ) + b = γ
    rw [hγ']
    linear_combination hγ
  obtain ⟨x, hx⟩ : ∃ x : ℂ, x ^ (2 : ℕ) = γ - b :=
    IsAlgClosed.exists_pow_nat_eq (γ - b) (by norm_num : 0 < 2)
  refine ⟨x, norm_le_one_of_sq hx hcond, ?_⟩
  -- orbit x ↦ γ ↦ γ' ↦ γ ↦ … lies in {x, γ, γ'}: reuse the three-point engine with a 2-cycle
  have horbit : ∀ n : ℕ, (quadratic b)^[n] x ∈ ({x, γ, γ'} : Set ℂ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
      rcases ih with h | h | h
      · have : quadratic b x = γ := by
          show x ^ (2 : ℕ) + b = γ
          rw [hx]; ring
        rw [h, this]; tauto
      · rw [h, h1]; tauto
      · rw [h, h2]; tauto
  rw [mem_filledJulia_iff]
  have hfin : ({x, γ, γ'} : Set ℂ).Finite := Set.toFinite _
  refine hfin.isBounded.subset ?_
  rw [Set.range_subset_iff]
  exact horbit

/-- **Preperiodicity implies a bounded orbit.**  If `y` is preperiodic under `f_b`
(`f^[k+n] y = f^[k] y` with `n ≥ 1`), its forward orbit is contained in the finite set
`{f^[j] y : j < k+n}`, hence `y ∈ K_b`.  This is the structural core behind every finite
obstruction certificate in the Cantor regime, where the only bounded orbits are preperiodic. -/
theorem filledJulia_of_preperiodic {b y : ℂ} {k n : ℕ} (hn : 1 ≤ n)
    (hper : (quadratic b)^[k + n] y = (quadratic b)^[k] y) :
    y ∈ filledJulia b := by
  rw [mem_filledJulia_iff]
  have hkey : ∀ m, k ≤ m → (quadratic b)^[m + n] y = (quadratic b)^[m] y := by
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [show k + d + n = d + (k + n) from by omega,
        Function.iterate_add_apply, hper, ← Function.iterate_add_apply,
        show d + k = k + d from by omega]
  have hreduce : ∀ m, ∃ j, j < k + n ∧ (quadratic b)^[m] y = (quadratic b)^[j] y := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hlt : m < k + n
      · exact ⟨m, hlt, rfl⟩
      · push Not at hlt
        have hmn : n ≤ m := le_trans (Nat.le_add_left n k) hlt
        have hkm : k ≤ m - n := by omega
        have hstep : (quadratic b)^[m] y = (quadratic b)^[m - n] y := by
          have := hkey (m - n) hkm
          rw [Nat.sub_add_cancel hmn] at this
          exact this
        obtain ⟨j, hj, hje⟩ := ih (m - n) (by omega)
        exact ⟨j, hj, hstep.trans hje⟩
  have hsub : Set.range (fun m : ℕ => (quadratic b)^[m] y) ⊆
      (fun j : ℕ => (quadratic b)^[j] y) '' (Set.Iio (k + n)) := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨j, hj, hje⟩ := hreduce m
    exact ⟨j, hj, hje.symm⟩
  exact (Set.Finite.image _ (Set.finite_Iio (k + n))).isBounded.subset hsub

/-- **The general preperiodic-entry obstruction.**  If `y` is preperiodic and `‖y − b‖ ≤ 1`,
the square root `x₀` of `y − b` (one step before `y`) lies in the closed unit disk and in `K_b`
— so `K_b` meets the closed unit disk.  P1 (`k=1, n=1`) and P2 (`k=0, n=2`) are the special
cases; the period-`n` lobe instances (`U0LobeInstances`) are `k=0, n=3`. -/
theorem filledJulia_meets_unit_disk_preperiodic {b y : ℂ} {k n : ℕ} (hn : 1 ≤ n)
    (hper : (quadratic b)^[k + n] y = (quadratic b)^[k] y) (hcond : ‖y - b‖ ≤ 1) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia b := by
  obtain ⟨x₀, hx₀⟩ : ∃ x : ℂ, x ^ (2 : ℕ) = y - b :=
    IsAlgClosed.exists_pow_nat_eq (y - b) (by norm_num : 0 < 2)
  refine ⟨x₀, norm_le_one_of_sq hx₀ hcond, ?_⟩
  have hfx : quadratic b x₀ = y := by show x₀ ^ (2 : ℕ) + b = y; rw [hx₀]; ring
  rw [mem_filledJulia_iff_quadratic_mem, hfx]
  exact filledJulia_of_preperiodic hn hper

/-- P1 re-derived from the general theorem (subsumption certificate): `y = −β` is preperiodic
with preperiod `1`, period `1`. -/
theorem filledJulia_meets_unit_disk_P1_via_prep {b s : ℂ} (hs : s ^ (2 : ℕ) = 1 - 4 * b)
    (hcond : ‖(1 + s) / 2 + b‖ ≤ 1) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia b := by
  set β : ℂ := (1 + s) / 2 with hβ
  have hβfix : β ^ (2 : ℕ) + b = β := by rw [hβ]; linear_combination hs / 4
  have e1 : quadratic b (-β) = β := by show (-β) ^ (2 : ℕ) + b = β; linear_combination hβfix
  have e2 : quadratic b β = β := hβfix
  refine filledJulia_meets_unit_disk_preperiodic (y := -β) (k := 1) (n := 1) le_rfl ?_ ?_
  · show quadratic b (quadratic b (-β)) = quadratic b (-β)
    rw [e1, e2]
  · rw [show -β - b = -(β + b) from by ring, norm_neg]; exact hcond

/-- P2 re-derived from the general theorem (subsumption certificate): `y = γ` is periodic with
preperiod `0`, period `2`. -/
theorem filledJulia_meets_unit_disk_P2_via_prep {b γ : ℂ} (hγ : γ ^ (2 : ℕ) + γ + b + 1 = 0)
    (hcond : ‖γ - b‖ ≤ 1) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia b := by
  set γ' : ℂ := -1 - γ with hγ'
  have h1 : quadratic b γ = γ' := by show γ ^ (2 : ℕ) + b = γ'; rw [hγ']; linear_combination hγ
  have h2 : quadratic b γ' = γ := by show γ' ^ (2 : ℕ) + b = γ; rw [hγ']; linear_combination hγ
  refine filledJulia_meets_unit_disk_preperiodic (y := γ) (k := 0) (n := 2) (by norm_num) ?_ hcond
  · show quadratic b (quadratic b γ) = γ
    rw [h1, h2]

/-- Cross-check at the rational-`s` grid point `s = 29/8`, `b = −777/256` (arg `b` = π,
`‖b‖ ≈ 3.035`): the P1 condition is pure rational arithmetic. -/
example : ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia ((-777 / 256 : ℂ)) := by
  refine filledJulia_meets_unit_disk_P1 (s := 29 / 8) (by norm_num) ?_
  have h : (1 + (29 / 8 : ℂ)) / 2 + (-777 / 256) = (((-185 / 256 : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_neg (by norm_num)]
  norm_num

end U0ObstructionPatterns
