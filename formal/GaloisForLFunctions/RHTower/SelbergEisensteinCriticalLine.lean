import GaloisForLFunctions.RHTower.SelbergEisensteinStarCriticalLine

open Complex UpperHalfPlane Metric Filter Topology
open scoped MatrixGroups

/-!
# The `Γ(N)` Eisenstein series at every cusp across the critical line

The scattering entry continues as `φ_{∞,σ∞}(s) = C(s) Σ_u L_u(2s) L(Φ_σ(u ·), 2s - 1)` (`phiExt`, equal to `phiσ` on
`Re s > 1/2` by the Beta integral and `L(μχ_N δ_u, 2s) = L_u(2s)`, `phiσ_eq_phiExt`), holomorphic on `W \ {1}`
(`differentiableAt_phiExt`: `L_u` off the zeros of `L(2s, χ)`, the periodic `L`-function off `s = 1`, and
`C(s) = √π Γ(s-1/2)/Γ(s)` off `s = 1/2 - m`). With the continued non-constant part `EstarExt`, the expansion
`EcuspExt(s, z) = count₀ y^s + N^{-s}(y/N)^{1-s} φ_{∞,σ∞}(s) + E^*_σ(z, s)` is holomorphic on `W \ {1}`
(`differentiableAt_EcuspExt`), and agrees with the continued Eisenstein series `E_∞(σz, s)` on `Re s > 1/2`, `s ≠ 1`
(`Econt_smul_eq_EcuspExt`, `N ≥ 3`). Since `W ⊇ {Re s ≥ 1/2, s ≠ 1/2}` (`mem_Wset_of_half_le`), every Eisenstein
series of `Γ(N)` is holomorphic on a neighbourhood of the critical line `Re s = 1/2` minus `s = 1/2`
(`differentiableAt_EcuspExt_of_half_le`): the continuous spectrum of `Γ(N)\ℍ`.
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCriticalLine
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier GaloisForLFunctions.RHTower.SelbergEisensteinCoefficientSeries
  GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL GaloisForLFunctions.RHTower.SelbergEisensteinStarCriticalLine
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspExpansion GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering
  GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry GaloisForLFunctions.RHTower.SelbergKernelBetaIntegral
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant GaloisForLFunctions.RHTower.SelbergPoincareContinuation

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- The continued scattering entry `φ_{∞,σ∞}(s) = C(s) Σ_u L_u(2s) L(Φ_σ(u ·), 2s - 1)`. -/
noncomputable def phiExt (s : ℂ) : ℂ :=
  (∑ u : (ZMod N)ˣ, LU N u (2 * s) * ZMod.LFunction (PhiU N (PhiS N σ) u) (2 * s - 1)) * cBeta s

theorem phiσ_eq_phiExt {s : ℂ} (hs : 1 / 2 < s.re) : phiσ N σ s = phiExt N σ s := by
  have hw : 1 < (2 * s).re := by simp; linarith
  unfold phiσ phiExt Dσ
  rw [integral_ker01 hs]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [LSeries_muChiU_eq N hw]

theorem differentiableAt_phiExt {s : ℂ} (hs : s ∈ Wset N) (hs1 : s ≠ 1) : DifferentiableAt ℂ (phiExt N σ) s := by
  obtain ⟨h0, h2, hL⟩ := hs
  unfold phiExt
  have e : (fun s : ℂ => ∑ u : (ZMod N)ˣ, LU N u (2 * s) * ZMod.LFunction (PhiU N (PhiS N σ) u) (2 * s - 1)) =
      ∑ u : (ZMod N)ˣ, fun s : ℂ => LU N u (2 * s) * ZMod.LFunction (PhiU N (PhiS N σ) u) (2 * s - 1) := by
    funext s; simp [Finset.sum_apply]
  refine DifferentiableAt.mul ?_ ?_
  · rw [e]
    refine DifferentiableAt.sum (fun u _ => ?_)
    refine ((differentiableAt_LU_of N u h2 hL).comp s (differentiableAt_id.const_mul 2)).mul ?_
    refine (ZMod.differentiableAt_LFunction _ _ (Or.inl ?_)).comp s ((differentiableAt_id.const_mul 2).sub_const 1)
    intro h; apply hs1; linear_combination h / 2
  · unfold cBeta
    refine ((differentiableAt_const _).mul ?_).mul (Complex.differentiable_one_div_Gamma s)
    refine (Complex.differentiableAt_Gamma _ (fun m hm => ?_)).comp s (differentiableAt_id.sub_const _)
    rcases m with _ | m
    · apply h2; simp at hm; linear_combination 2 * hm
    · have := congrArg Complex.re hm
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith

/-- **The continued Eisenstein series at the cusp `σ∞`**: holomorphic on `W \ {1}`. -/
noncomputable def EcuspExt (s : ℂ) (z : ℍ) : ℂ :=
  ((z.im : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) +
    cexp (-s * (Real.log N : ℂ)) * (((z.im / N : ℝ)) : ℂ) ^ (1 - s) * phiExt N σ s + EstarExt N σ s z

theorem Ecusp_eq_EcuspExt {s : ℂ} (hs : 1 / 2 < s.re) (z : ℍ) : Ecusp N σ s z = EcuspExt N σ s z := by
  unfold Ecusp EcuspExt
  rw [phiσ_eq_phiExt N σ hs, Estarσ_eq_EstarExt N σ hs z]

theorem differentiableAt_EcuspExt (z : ℍ) {s : ℂ} (hs : s ∈ Wset N) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => EcuspExt N σ s z) s := by
  unfold EcuspExt
  have hy : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  have hyN : (((z.im / N : ℝ)) : ℂ) ≠ 0 := by
    have : 0 < z.im / N := div_pos z.im_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    exact_mod_cast this.ne'
  refine (((differentiableAt_id.const_cpow (Or.inl hy)).mul_const _).add ?_).add
    (differentiableAt_EstarExt N σ z hs)
  exact (((differentiable_exp_neg_mul _).differentiableAt).mul
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id |>.const_cpow (Or.inl hyN))).mul
    (differentiableAt_phiExt N σ hs hs1)

/-- **The `Γ(N)` Eisenstein series at every cusp across the critical line** (`N ≥ 3`): the continued
`E_∞(σz, s)` coincides on `Re s > 1/2`, `s ≠ 1` with `EcuspExt`, which is holomorphic on the open set `W \ {1}`;
`W` contains every `s` with `Re s ≥ 1/2`, `s ≠ 1/2`. -/
theorem Econt_smul_eq_EcuspExt (hN : 3 ≤ N) (z : ℍ) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    Econt N s (σ • z) = EcuspExt N σ s z := by
  rw [Econt_smul_eq N σ hN z hs hs1, Ecusp_eq_EcuspExt N σ hs z]

theorem differentiableAt_EcuspExt_of_half_le (z : ℍ) {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs12 : s ≠ 1 / 2)
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (fun s => EcuspExt N σ s z) s :=
  differentiableAt_EcuspExt N σ z (mem_Wset_of_half_le N hs hs12) hs1

end GaloisForLFunctions.RHTower.SelbergEisensteinCriticalLine
