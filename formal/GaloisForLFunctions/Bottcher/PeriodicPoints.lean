/-
# Böttcher tower — existence of periodic points (entry to the interior natural boundary, D2)

The interior-Fatou-component case of the `J_c` natural boundary runs on **repelling periodic points**:
at a period-`p` point `z₀` with multiplier `λ` (`|λ|>1`), a hypothetical continuation of `φ_c` forces
the resonance `λ^m = 2^p` (from `φ_c(f^p z)=φ_c(z)^{2^p}`), impossible for nonexceptional `c`. The
entry point is the existence of periodic points: `f_c^[p] z = z` has a solution, because `f_c^[p]` is a
polynomial of degree `2^p` and `f_c^[p](z) - z` is a nonconstant polynomial over the algebraically
closed `ℂ`.

New file (hRigid connected lane, D2 foundation); consumes `BasinBranching`.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Polynomial

namespace Bottcher

/-- **Periodic points exist.** For every period `p ≥ 1`, `f_c^[p]` has a fixed point (a periodic point
of `f_c` of period dividing `p`): `f_c^[p] z - z` is a degree-`2^p` polynomial over `ℂ`, hence has a
root. The dynamical foundation of the repelling-cycle route to the interior `J_c` natural boundary. -/
theorem exists_periodic_point (c : ℂ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ z : ℂ, (quadratic c)^[p] z = z := by
  have hXlt : (Polynomial.X : Polynomial ℂ).natDegree < (quadraticPolyIterate c p).natDegree := by
    rw [Polynomial.natDegree_X, quadraticPolyIterate_natDegree]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  have hdeg : (quadraticPolyIterate c p - Polynomial.X).natDegree = 2 ^ p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hXlt, quadraticPolyIterate_natDegree]
  have hdegpos : 0 < (quadraticPolyIterate c p - Polynomial.X).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hdeg]; positivity)
  obtain ⟨z, hz⟩ := Complex.exists_root hdegpos
  have hz' : (quadraticPolyIterate c p - Polynomial.X).eval z = 0 := hz
  rw [Polynomial.eval_sub, Polynomial.eval_X, quadraticPolyIterate_eval, sub_eq_zero] at hz'
  exact ⟨z, hz'⟩

/-- **A periodic point lies in the filled Julia set.** A period-`p` point (`f_c^[p] z = z`, `p ≥ 1`) has a
finite forward orbit (`f_c^[n] z = f_c^[n % p] z`, valued in `{f_c^[k] z : k < p}`), hence a bounded one, so
`z ∈ K_c`. The location half of the repelling-cycle datum, for all periods. -/
theorem mem_filledJulia_of_periodic {c z : ℂ} {p : ℕ} (hp : 1 ≤ p)
    (hper : (quadratic c)^[p] z = z) : z ∈ filledJulia c := by
  rw [mem_filledJulia_iff]
  have hpp : Function.IsPeriodicPt (quadratic c) p z := hper
  have hsub : (Set.range fun n : ℕ => (quadratic c)^[n] z)
      ⊆ (fun k => (quadratic c)^[k] z) '' (Set.Iio p) := by
    rintro x ⟨n, rfl⟩
    exact ⟨n % p, Nat.mod_lt n hp, hpp.iterate_mod_apply n⟩
  exact (Set.Finite.subset ((Set.finite_Iio p).image _) hsub).isBounded

/-- A fixed point of `f_c` lies in the filled Julia set (its orbit is the constant `{z₀}`). -/
theorem mem_filledJulia_of_fixed {c z₀ : ℂ} (h : quadratic c z₀ = z₀) : z₀ ∈ filledJulia c := by
  rw [mem_filledJulia_iff]
  have horbit : ∀ n : ℕ, (quadratic c)^[n] z₀ = z₀ := fun n => Function.iterate_fixed h n
  rw [show (fun n : ℕ => (quadratic c)^[n] z₀) = fun _ => z₀ from funext horbit, Set.range_const]
  exact Bornology.isBounded_singleton

/-- **A repelling-or-neutral fixed point exists, in the Julia set.** The two fixed points `z±` of
`f_c(z)=z²+c` (roots of `z²-z+c`) have multipliers `2z±` summing (Vieta) to `2`, so
`‖2z₊‖+‖2z₋‖ ≥ ‖2z₊+2z₋‖ = 2` and at least one has multiplier modulus `≥ 1` — a fixed point in
`filledJulia c` that is NOT attracting (hence on the Julia boundary `J_c`). The elementary seed of the
repelling-cycle datum the connected-case obstruction needs: a concrete periodic point of `f_c` in `K_c`
with `‖λ‖ ≥ 1`. (Strengthening to strict repulsion / non-resonance / location off `filledJulia c₂` is the
remaining Fatou-density content.) -/
theorem exists_fixed_point_multiplier_ge_one (c : ℂ) :
    ∃ z₀ : ℂ, quadratic c z₀ = z₀ ∧ z₀ ∈ filledJulia c ∧ 1 ≤ ‖(2 : ℂ) * z₀‖ := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (1 - 4 * c) (n := 2) (by norm_num)
  set zp : ℂ := (1 + s) / 2 with hzp
  set zm : ℂ := (1 - s) / 2 with hzm
  have hzp_fix : quadratic c zp = zp := by
    show zp ^ 2 + c = zp; rw [hzp]; field_simp; linear_combination hs
  have hzm_fix : quadratic c zm = zm := by
    show zm ^ 2 + c = zm; rw [hzm]; field_simp; linear_combination hs
  have hmul : (2 : ℂ) * zp + (2 : ℂ) * zm = 2 := by rw [hzp, hzm]; ring
  have hsum : (2 : ℝ) ≤ ‖(2 : ℂ) * zp‖ + ‖(2 : ℂ) * zm‖ := by
    calc (2 : ℝ) = ‖(2 : ℂ) * zp + (2 : ℂ) * zm‖ := by rw [hmul]; norm_num
      _ ≤ ‖(2 : ℂ) * zp‖ + ‖(2 : ℂ) * zm‖ := norm_add_le _ _
  by_cases hp : 1 ≤ ‖(2 : ℂ) * zp‖
  · exact ⟨zp, hzp_fix, mem_filledJulia_of_fixed hzp_fix, hp⟩
  · push_neg at hp
    exact ⟨zm, hzm_fix, mem_filledJulia_of_fixed hzm_fix, by linarith⟩

/-- **A strictly repelling fixed point exists (for `c ≠ 1/4`).** If neither fixed point `z±` were
repelling (`‖2z±‖ ≤ 1`), the parallelogram law `‖1+s‖²+‖1-s‖² = 2(‖1‖²+‖s‖²) = 2+2‖s‖²` (with
`2z±=1±s`, `s²=1-4c`) would force `2+2‖s‖² ≤ 2`, i.e. `s=0`, i.e. `c=1/4`. So for `c ≠ 1/4` one fixed
point has multiplier modulus `> 1` — a strictly repelling fixed point in `K_c` (hence on `J_c`). The
single excluded value `c=1/4` is the parabolic root of the main cardioid (the `α`-fixed-point multiplier
`= 1`), an exceptional parameter. This sharpens `exists_fixed_point_multiplier_ge_one` to strict
repulsion, the next datum toward the repelling-cycle input of `hrig_phiMero_of_repelling`. -/
theorem exists_repelling_fixed_point (c : ℂ) (hc : c ≠ 1 / 4) :
    ∃ z₀ : ℂ, quadratic c z₀ = z₀ ∧ z₀ ∈ filledJulia c ∧ 1 < ‖(2 : ℂ) * z₀‖ := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (1 - 4 * c) (n := 2) (by norm_num)
  have hs0 : s ≠ 0 := by
    intro h; apply hc
    have : (1 : ℂ) - 4 * c = 0 := by rw [← hs, h]; ring
    linear_combination -(1 / 4) * this
  set zp : ℂ := (1 + s) / 2 with hzp
  set zm : ℂ := (1 - s) / 2 with hzm
  have hzp_fix : quadratic c zp = zp := by
    show zp ^ 2 + c = zp; rw [hzp]; field_simp; linear_combination hs
  have hzm_fix : quadratic c zm = zm := by
    show zm ^ 2 + c = zm; rw [hzm]; field_simp; linear_combination hs
  have h2p : (2 : ℂ) * zp = 1 + s := by rw [hzp]; ring
  have h2m : (2 : ℂ) * zm = 1 - s := by rw [hzm]; ring
  have hpar : ‖(1 : ℂ) + s‖ ^ 2 + ‖(1 : ℂ) - s‖ ^ 2 = 2 * (‖(1 : ℂ)‖ ^ 2 + ‖s‖ ^ 2) :=
    parallelogram_law_with_norm ℝ (1 : ℂ) s
  have hsnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  by_contra hcon
  push_neg at hcon
  have hple : ‖(1 : ℂ) + s‖ ≤ 1 := by
    have := hcon zp hzp_fix (mem_filledJulia_of_fixed hzp_fix); rwa [h2p] at this
  have hmle : ‖(1 : ℂ) - s‖ ≤ 1 := by
    have := hcon zm hzm_fix (mem_filledJulia_of_fixed hzm_fix); rwa [h2m] at this
  have hp2 : ‖(1 : ℂ) + s‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ((1 : ℂ) + s), hple]
  have hm2 : ‖(1 : ℂ) - s‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ((1 : ℂ) - s), hmle]
  have hone : ‖(1 : ℂ)‖ = 1 := by norm_num
  rw [hone] at hpar
  nlinarith [hpar, hp2, hm2, hsnorm]

/-- **Two distinct fixed points (`c ≠ 1/4`).** The fixed-point equation `z²+c=z` is `z²-z+c=0` with
discriminant `1-4c ≠ 0`, so its two roots `(1±s)/2` (`s²=1-4c`, `s≠0`) are distinct fixed points of `f_c`.
The base data of Milnor's cross-ratio density argument (the two anchor values of the cross-ratio family). -/
theorem exists_two_distinct_fixed_points (c : ℂ) (hc : c ≠ 1 / 4) :
    ∃ α β : ℂ, quadratic c α = α ∧ quadratic c β = β ∧ α ≠ β := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (1 - 4 * c) (n := 2) (by norm_num)
  have hs0 : s ≠ 0 := by
    intro h; apply hc
    have : (1 : ℂ) - 4 * c = 0 := by rw [← hs, h]; ring
    linear_combination -(1 / 4) * this
  refine ⟨(1 + s) / 2, (1 - s) / 2, ?_, ?_, ?_⟩
  · show ((1 + s) / 2) ^ 2 + c = (1 + s) / 2; field_simp; linear_combination hs
  · show ((1 - s) / 2) ^ 2 + c = (1 - s) / 2; field_simp; linear_combination hs
  · intro h
    apply hs0
    have : (1 + s) / 2 - (1 - s) / 2 = 0 := by rw [h]; ring
    linear_combination this

/-- **Cross-ratio `= 1 ⟺ periodic`.** For distinct `α, β` and a point `z` with `w ≠ β`, `z ≠ α`, the
cross-ratio `(w-α)(z-β) / ((w-β)(z-α)) = 1` iff `w = z`. With `w = f_c^[n] z`, this is the heart of Milnor's
density argument: the cross-ratio family `z ↦ (f^[n]z-α)(z-β)/((f^[n]z-β)(z-α))` takes the value `1` at `z`
exactly at the period-`n` points — so a periodic-point-free disk makes the family omit `1`, which (with
`0,∞` excluded by preimages of `α,β`) feeds the three-value Montel normality, contradicting non-normality
at a Julia point. -/
theorem crossRatio_eq_one_iff {α β z w : ℂ} (hαβ : α ≠ β) (hwβ : w ≠ β) (hzα : z ≠ α) :
    (w - α) * (z - β) / ((w - β) * (z - α)) = 1 ↔ w = z := by
  rw [div_eq_one_iff_eq (mul_ne_zero (sub_ne_zero.mpr hwβ) (sub_ne_zero.mpr hzα))]
  constructor
  · intro h
    have hcancel : (w - z) * (α - β) = 0 := by ring_nf; ring_nf at h; linear_combination h
    rcases mul_eq_zero.mp hcancel with h1 | h2
    · exact sub_eq_zero.mp h1
    · exact absurd (sub_eq_zero.mp h2) hαβ
  · intro h; rw [h]; ring

/-- **Cross-ratio `= 0 ⟺` numerator zero.** `(w-α)(z-β)/((w-β)(z-α)) = 0` (denominator nonzero) iff
`w = α` or `z = β`. With `w = f_c^[n] z`, the family hits `0` exactly at the `α`-preimages and at `z = β` —
the first extra omitted value (excludable by removing the countable preimage set). -/
theorem crossRatio_eq_zero_iff {α β z w : ℂ} (hwβ : w ≠ β) (hzα : z ≠ α) :
    (w - α) * (z - β) / ((w - β) * (z - α)) = 0 ↔ w = α ∨ z = β := by
  rw [div_eq_zero_iff]
  have hden : (w - β) * (z - α) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hwβ) (sub_ne_zero.mpr hzα)
  simp only [hden, or_false, mul_eq_zero, sub_eq_zero]

/-- **Cross-ratio family is holomorphic off the `β`-fibre.** Where `f_c^[n] z ≠ β` and `z ≠ α` (denominator
nonzero), the cross-ratio `z ↦ (f^[n]z-α)(z-β)/((f^[n]z-β)(z-α))` is differentiable — a rational expression
in the entire `f_c^[n]` and `z`. The analytic input the three-value Montel (`normal_of_omitting_lift`)
consumes when establishing density of periodic points. -/
theorem differentiableAt_crossRatio {c α β : ℂ} {n : ℕ} {z : ℂ}
    (hwβ : (quadratic c)^[n] z ≠ β) (hzα : z ≠ α) :
    DifferentiableAt ℂ
      (fun z => ((quadratic c)^[n] z - α) * (z - β) / (((quadratic c)^[n] z - β) * (z - α))) z := by
  have hiter : ∀ m : ℕ, Differentiable ℂ ((quadratic c)^[m]) := by
    intro m
    induction m with
    | zero => simpa using differentiable_id
    | succ k ih =>
      rw [Function.iterate_succ']
      exact (by unfold quadratic; fun_prop : Differentiable ℂ (quadratic c)).comp ih
  have hfdiff : DifferentiableAt ℂ ((quadratic c)^[n]) z := (hiter n) z
  have hnum : DifferentiableAt ℂ
      (fun z => ((quadratic c)^[n] z - α) * (z - β)) z :=
    (hfdiff.sub_const α).mul (show DifferentiableAt ℂ (fun z : ℂ => z - β) z by fun_prop)
  have hden : DifferentiableAt ℂ
      (fun z => ((quadratic c)^[n] z - β) * (z - α)) z :=
    (hfdiff.sub_const β).mul (show DifferentiableAt ℂ (fun z : ℂ => z - α) z by fun_prop)
  have hdne : ((quadratic c)^[n] z - β) * (z - α) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hwβ) (sub_ne_zero.mpr hzα)
  exact hnum.div hden hdne

end Bottcher
