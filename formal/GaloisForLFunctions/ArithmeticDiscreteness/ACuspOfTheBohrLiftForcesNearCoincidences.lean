import GaloisForLFunctions.ArithmeticDiscreteness.ConsistentTangenciesForceNearCoincidences
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A cusp of the Bohr lift forces near-coincidences

Near-coincidences at every scale are not special to Euler products. The integral carrier

`D(s) = (1 − 2^{−s})² − (1 − 3^{−s})³`

is not a product of local factors, and its Bohr lift `G(x, y) = (1 − x)² − (1 − y)³` has a cusp at
the torsion point `(1, 1)`, which is consistent (`σ = 0`). Along the lift through it,
`f(w) = (1 − 2^{−w})² − (1 − 3^{−w})³ = w² k(w)` with `k(0) = (log 2)² ≠ 0`
(`cuspLift_eq_sq_mul`), so the tangency is isolated of order two (`zeroMult_cuspLift`).

* **Near-coincidences at every scale** (`cuspCarrier_collision_or_close_pair`). For every `δ > 0`
  and `T₀` there is `t > T₀` such that within `δ` of `it` the carrier has a multiple zero or two
  distinct zeros (`exists_collision_or_close_pair`).

For two primes and integer coefficients a consistent tangency at a torsion point must be a singular
point of `G` (`log 2/log 3 ∉ ℚ` kills the tangency equation `x G_x log 2 + y G_y log 3 = 0`
otherwise); the Euler product has a node there, this carrier a cusp.
-/

open Complex Metric Filter

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The primes `2, 3`. -/
def primesTwoThree : Fin 2 → Nat.Primes := ![⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩]

theorem primesTwoThree_injective : Function.Injective primesTwoThree := by
  intro a b h
  have hv := congrArg Subtype.val h
  fin_cases a <;> fin_cases b <;> simp [primesTwoThree] at hv ⊢

/-- The Bohr lift `(1 − x)² − (1 − y)³`. -/
def cuspLift (x : Fin 2 → ℂ) : ℂ := (1 - x 0) ^ 2 - (1 - x 1) ^ 3

/-- The carrier `(1 − 2^{−s})² − (1 − 3^{−s})³`. -/
def cuspCarrier (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (-s)) ^ 2 - (1 - (3 : ℂ) ^ (-s)) ^ 3

theorem translateCarrier_cusp (v : Fin 2 → ℂ) (s : ℂ) :
    translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift v s =
      (1 - v 0 * (2 : ℂ) ^ (-s)) ^ 2 - (1 - v 1 * (3 : ℂ) ^ (-s)) ^ 3 := by
  simp [translateCarrier, cuspLift, primesTwoThree]

theorem translateCarrier_cusp_one :
    translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift 1 = cuspCarrier := by
  funext s; rw [translateCarrier_cusp]; simp [cuspCarrier]

theorem differentiable_cpow_neg {c : ℂ} (hc : c ≠ 0) : Differentiable ℂ fun s : ℂ => c ^ (-s) :=
  differentiable_neg.const_cpow (Or.inl hc)

/-- `g_c(w) = 1 − c^{−w}` vanishes at `0` with derivative `log c`. -/
theorem hasDerivAt_one_sub_cpow_neg {c : ℂ} (hc : c ≠ 0) :
    HasDerivAt (fun w : ℂ => 1 - c ^ (-w)) (Complex.log c) 0 := by
  have h := ((hasDerivAt_neg (0 : ℂ)).const_cpow (c := c) (Or.inl hc)).const_sub 1
  simpa using h

/-- **The lift through the cusp is `w² k(w)`** with `k(0) = (log 2)²`. -/
theorem cuspLift_eq_sq_mul :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ k 0 = Complex.log 2 ^ 2 ∧
      ∀ w, cuspCarrier w = w ^ 2 * k w := by
  set g : ℂ → ℂ := fun w => 1 - (2 : ℂ) ^ (-w) with hg
  set h : ℂ → ℂ := fun w => 1 - (3 : ℂ) ^ (-w) with hh
  have hgd : Differentiable ℂ g := (differentiable_const _).sub (differentiable_cpow_neg two_ne_zero)
  have hhd : Differentiable ℂ h :=
    (differentiable_const _).sub (differentiable_cpow_neg three_ne_zero)
  have hg0 : g 0 = 0 := by simp [hg]
  have hh0 : h 0 = 0 := by simp [hh]
  have hdg : Differentiable ℂ (dslope g 0) := fun z =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hgd.differentiableOn z
      (Set.mem_univ z)).differentiableAt Filter.univ_mem
  have hdh : Differentiable ℂ (dslope h 0) := fun z =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hhd.differentiableOn z
      (Set.mem_univ z)).differentiableAt Filter.univ_mem
  refine ⟨fun w => dslope g 0 w ^ 2 - w * dslope h 0 w ^ 3, (hdg.pow 2).sub
    (differentiable_id.mul (hdh.pow 3)), ?_, fun w => ?_⟩
  · simp only [zero_mul, sub_zero]
    rw [dslope_same, (hasDerivAt_one_sub_cpow_neg two_ne_zero).deriv]
  · have hgw := sub_smul_dslope_of_zero hg0 w
    have hhw := sub_smul_dslope_of_zero hh0 w
    simp only [sub_zero, smul_eq_mul] at hgw hhw
    have hc : cuspCarrier w = g w ^ 2 - h w ^ 3 := rfl
    rw [hc, ← hgw, ← hhw]
    ring

/-- **The tangency has order two.** -/
theorem zeroMult_cuspCarrier : HTGeometry.zeroMult cuspCarrier 0 = 2 := by
  obtain ⟨k, hk, hk0, hf⟩ := cuspLift_eq_sq_mul
  have hl2 : Complex.log 2 ≠ 0 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have han : AnalyticAt ℂ cuspCarrier 0 := by
    have : cuspCarrier = fun w => w ^ 2 * k w := funext hf
    rw [this]
    exact (differentiable_id.pow 2 |>.mul hk).analyticAt 0
  have hord : analyticOrderAt cuspCarrier 0 = (2 : ℕ) :=
    (han.analyticOrderAt_eq_natCast).mpr ⟨k, hk.analyticAt 0, by rw [hk0]; exact pow_ne_zero 2 hl2,
      Eventually.of_forall fun z => by rw [hf z, sub_zero, smul_eq_mul]⟩
  rw [HTGeometry.zeroMult, hord]; rfl

/-- **The tangency is isolated.** -/
theorem exists_isolation_cuspCarrier :
    ∃ ρ > 0, ∀ w ∈ closedBall (0 : ℂ) ρ, cuspCarrier w = 0 → w = 0 := by
  obtain ⟨k, hk, hk0, hf⟩ := cuspLift_eq_sq_mul
  have hl2 : k 0 ≠ 0 := by
    rw [hk0]
    refine pow_ne_zero 2 ?_
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hk.continuous.continuousAt.eventually_ne hl2)
  refine ⟨ε / 2, half_pos hε, fun w hw h0 => ?_⟩
  have hkw : k w ≠ 0 := hball (lt_of_le_of_lt (mem_closedBall.mp hw) (half_lt_self hε))
  rw [hf w] at h0
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ((mul_eq_zero.mp h0).resolve_right hkw)

/-- **Near-coincidences at every scale.** For every `δ > 0` and `T₀` there is `t > T₀` such that
`(1 − 2^{−s})² − (1 − 3^{−s})³` has, within `δ` of `it`, a multiple zero or two distinct zeros. -/
theorem cuspCarrier_collision_or_close_pair {δ : ℝ} (hδ : 0 < δ) (T₀ : ℝ) :
    ∃ t : ℝ, T₀ < t ∧
      ((∃ z ∈ ball (0 : ℂ) δ, cuspCarrier (t * I + z) = 0 ∧
          2 ≤ HTGeometry.zeroMult (fun w => cuspCarrier (t * I + w)) z) ∨
        ∃ z ∈ ball (0 : ℂ) δ, ∃ z' ∈ ball (0 : ℂ) δ, z ≠ z' ∧
          cuspCarrier (t * I + z) = 0 ∧ cuspCarrier (t * I + z') = 0) := by
  obtain ⟨ρ, hρ, hiso⟩ := exists_isolation_cuspCarrier
  have hlift : ∀ w, translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift
      (fun _ => 1) (((0 : ℝ) : ℂ) + w) = cuspCarrier w := fun w => by
    rw [translateCarrier_cusp]; simp [cuspCarrier]
  have hcont : Continuous cuspLift :=
    ((continuous_const.sub (continuous_apply 0)).pow 2).sub
      ((continuous_const.sub (continuous_apply 1)).pow 3)
  have hhol : ∀ v : Fin 2 → ℂ,
      Differentiable ℂ (translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift v) := by
    intro v
    have : translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift v =
        fun s => (1 - v 0 * (2 : ℂ) ^ (-s)) ^ 2 - (1 - v 1 * (3 : ℂ) ^ (-s)) ^ 3 :=
      funext (translateCarrier_cusp v)
    rw [this]
    exact (((differentiable_const _).sub ((differentiable_const _).mul
      (differentiable_cpow_neg two_ne_zero))).pow 2).sub
      (((differentiable_const _).sub ((differentiable_const _).mul
      (differentiable_cpow_neg three_ne_zero))).pow 3)
  have hord : 2 ≤ HTGeometry.zeroMult (fun w => translateCarrier
      (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift (fun _ => 1) (((0 : ℝ) : ℂ) + w)) 0 := by
    rw [show (fun w => translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift
      (fun _ => 1) (((0 : ℝ) : ℂ) + w)) = cuspCarrier from funext hlift, zeroMult_cuspCarrier]
  obtain ⟨t, ht, hres⟩ := exists_collision_or_close_pair primesTwoThree primesTwoThree_injective
    hcont hhol (u := fun _ => 1) (fun _ => norm_one) (by simpa using (hlift 0).trans (by
      simp [cuspCarrier])) hρ (fun w hw h0 => hiso w hw (by rw [← hlift]; exact h0)) hord hδ T₀
  have hshift : ∀ w, translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift 1
      (((0 : ℝ) : ℂ) + t * I + w) = cuspCarrier (t * I + w) := fun w => by
    rw [translateCarrier_cusp_one]; simp
  refine ⟨t, ht, ?_⟩
  rcases hres with ⟨z, hz, hz0, hm⟩ | ⟨z, hz, z', hz', hne, h1, h2⟩
  · refine Or.inl ⟨z, hz, by rw [← hshift]; exact hz0, ?_⟩
    have : (fun w => translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) cuspLift 1
        (((0 : ℝ) : ℂ) + t * I + w)) = fun w => cuspCarrier (t * I + w) := funext hshift
    rwa [this] at hm
  · exact Or.inr ⟨z, hz, z', hz', hne, by rw [← hshift]; exact h1, by rw [← hshift]; exact h2⟩

end GaloisForLFunctions.ArithmeticDiscreteness
