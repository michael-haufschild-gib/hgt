import GaloisForLFunctions.RHTower.WeilLogShiftC0RecoveryReceiver

/-!
# A common vanishing envelope for finite-dimensional C₀ families

Finite basis expansion turns individual vanishing into one nonnegative
vanishing profile controlling every amplitude. Homogenization gives the
same profile for values and differences on regular affine fibres.
-/

open Filter Topology Real
open scoped ZeroAtInfty

noncomputable section

namespace RHTower

/-- A finite-dimensional linear family of `C₀` functions admits one
nonnegative vanishing profile, linear in the amplitude norm. -/
theorem exists_finiteDimensional_c0_vanishing_envelope
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] (S : E →ₗ[ℝ] C₀(X, ℝ)) :
    ∃ g : C₀(X, ℝ), (∀ x, 0 ≤ g x) ∧ ∀ (a : E) (x : X), |S a x| ≤ ‖a‖ * g x := by
  let b := Module.finBasis ℝ E
  let C := ‖b.equivFunL.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg b.equivFunL.toContinuousLinearMap
  have hcoord (a : E) (i : Fin (Module.finrank ℝ E)) : |b.equivFun a i| ≤ C * ‖a‖ := by
    calc
      _ = ‖b.equivFunL a i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖b.equivFunL a‖ := norm_le_pi_norm _ i
      _ ≤ C * ‖a‖ := b.equivFunL.toContinuousLinearMap.le_opNorm a
  let g : C₀(X, ℝ) := {
    toFun := fun x => C * ∑ i, |S (b i) x|
    continuous_toFun := continuous_const.mul
      (continuous_finsetSum _ (fun i _ => (map_continuous (S (b i))).abs))
    zero_at_infty' := by
      have ht (i : Fin (Module.finrank ℝ E)) :
          Tendsto (fun x => |S (b i) x|) (cocompact X) (𝓝 0) := by
        simpa only [Real.norm_eq_abs, abs_zero] using (zero_at_infty (S (b i))).norm
      have hsum : Tendsto (fun x => ∑ i, |S (b i) x|) (cocompact X) (𝓝 0) := by
        simpa only [Finset.sum_const_zero] using
          tendsto_finsetSum Finset.univ (fun i _ => ht i)
      simpa only [mul_zero] using hsum.const_mul C }
  have hrepr (a : E) (x : X) : S a x = ∑ i, b.equivFun a i * S (b i) x := by
    let p : E →ₗ[ℝ] ℝ := {
      toFun := fun a => S a x
      map_add' := fun a b => congrArg (fun f : C₀(X, ℝ) => f x) (map_add S a b)
      map_smul' := fun c a => congrArg (fun f : C₀(X, ℝ) => f x) (map_smul S c a) }
    change p a = ∑ i, b.equivFun a i * p (b i)
    calc
      p a = p (∑ i, b.equivFun a i • b i) := by rw [b.sum_equivFun]
      _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
  refine ⟨g, ?_, ?_⟩
  · intro x
    exact mul_nonneg hC (Finset.sum_nonneg (fun i _ => abs_nonneg (S (b i) x)))
  · intro a x
    change |S a x| ≤ ‖a‖ * (C * ∑ i, |S (b i) x|)
    calc
      _ = |∑ i, b.equivFun a i * S (b i) x| := congrArg abs (hrepr a x)
      _ ≤ ∑ i, |b.equivFun a i * S (b i) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (C * ‖a‖) * |S (b i) x| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hcoord a i) (abs_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring

/-- A single vanishing profile controls both values and amplitude sensitivity
of the common normalized receiver on the whole regular affine fibre. -/
theorem exists_weilLogShift_affine_vanishing_profile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E →ᵃ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (B : ℝ), 0 < B ∧ ∃ g : C₀(ℝ, ℝ), (∀ y, 0 ≤ g y) ∧
      ∃ Φ : {a : E // WeilLogShiftHasFactorialMajorant (F a)} → C₀(ℝ, ℝ),
        (∀ (a : {a : E // WeilLogShiftHasFactorialMajorant (F a)}) (y : ℝ),
          HasSum (fun n : ℕ => exp (-(B * n)) *
            (F (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) (Φ a y)) ∧
        (∀ a y, |Φ a y| ≤ (1 + ‖(a : E)‖) * g y) ∧
        ∀ a b y, |Φ a y - Φ b y| ≤ ‖(a : E) - (b : E)‖ * g y := by
  let H : (E × ℝ) →ₗ[ℝ] (ℕ → ℝ) :=
    F.linear.comp (LinearMap.fst ℝ E ℝ) + (LinearMap.snd ℝ E ℝ).smulRight (F 0)
  have heq (a : E) : H (a, 1) = F a := by
    change F.linear a + (1 : ℝ) • F 0 = F a
    simpa only [one_smul, vadd_eq_add, add_zero] using (F.map_vadd (0 : E) a).symm
  obtain ⟨m, B, _, hB, _, S, _, hvalue⟩ := exists_weilLogShift_uniform_c0_operator H
  obtain ⟨g, hg, hprofile⟩ := exists_finiteDimensional_c0_vanishing_envelope S.toLinearMap
  let L : Submodule ℝ (E × ℝ) := weilLogShiftFactorialSequenceSubmodule.comap H
  let lift : {a : E // WeilLogShiftHasFactorialMajorant (F a)} → L := fun a =>
    ⟨((a : E), 1), by
      change WeilLogShiftHasFactorialMajorant (H ((a : E), 1))
      rw [heq]
      exact a.property⟩
  let Φ : {a : E // WeilLogShiftHasFactorialMajorant (F a)} → C₀(ℝ, ℝ) := fun a => S (lift a)
  refine ⟨m, B, hB, g, hg, Φ, ?_, ?_, ?_⟩
  · intro a y
    simpa only [lift, heq] using hvalue (lift a) y
  · intro a y
    have hn : ‖lift a‖ ≤ 1 + ‖(a : E)‖ := by
      change ‖((a : E), (1 : ℝ))‖ ≤ 1 + ‖(a : E)‖
      rw [Prod.norm_def, norm_one]
      exact max_le (by linarith [norm_nonneg (a : E)]) (by linarith [norm_nonneg (a : E)])
    exact (hprofile (lift a) y).trans (mul_le_mul_of_nonneg_right hn (hg y))
  · intro a b y
    have hd : ‖lift a - lift b‖ = ‖(a : E) - (b : E)‖ := by
      change ‖((a : E) - (b : E), (1 : ℝ) - 1)‖ = ‖(a : E) - (b : E)‖
      rw [sub_self, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
    have he : S (lift a - lift b) y = Φ a y - Φ b y :=
      congrArg (fun f : C₀(ℝ, ℝ) => f y) (map_sub S (lift a) (lift b))
    rw [← he]
    exact (hprofile (lift a - lift b) y).trans_eq (by rw [hd])

end RHTower
